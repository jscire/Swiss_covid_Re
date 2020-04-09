rm(list=ls())

library("ggplot2")
library("lubridate")
library("readr")
library("EpiEstim")
library("gridExtra")
library("reshape2")
library(RColorBrewer)
library(reshape)
library(ggpubr)
library(wesanderson)

### Help function for plotting
gg_color <- function(n) {
  
  hues = seq(15, 375, length = n + 1)
  
  hcl(h = hues, l = 65, c = 100)[1:n]
  
}


### Function made to account for missing entries in data
## 
## Makes linear interpolation of missing values
## 
## For dates after 'startDate' if two consecutive reports of cumulative cases are equal, replaces the second one by an interpolation with the entry from the previous and next day
## This is done to account for days when the confirmed case data was not updated
##  
## The function assumes that entry data "cumulDataVector" is either given, 
## or has an NA, for all days of the calendar (no day is skipped entirely)
fillInMissingCumulativeData <- function(dates, cumulDataVector, startDate="2020-03-12"){
  
  if(sum(is.na(cumulDataVector)) > 0 & sum(!is.na(cumulDataVector)) > 1) {
    known_dates <- dates[!is.na(cumulDataVector)]
    cumulDataVector <- na.omit(cumulDataVector)
    
    interpolated_cases <- floor(approx(known_dates, cumulDataVector, xout = dates)$y) 
  } else { # no missing data, no interpolation needed
    interpolated_cases <- cumulDataVector
  }
  
  ## interpolate number of confirmed cases for consecutive equal entries (no reporting on the second day)
  for(i in which(dates == startDate):(length(interpolated_cases) -1)) {
    if(!is.na(interpolated_cases[i]) & !is.na(interpolated_cases[i-1])) {
      if(interpolated_cases[i] == interpolated_cases[i-1]) {
        interpolated_cases[i] <- floor((interpolated_cases[i-1] + interpolated_cases[i+1]) / 2)
      }
    }
  }
  
  return(interpolated_cases)
}

## Get incidence data from cumulative counts data and restructure dataframe
## Any data after 'stoppingDate' is excluded
meltCumulativeData <- function(rawData, dataType, stoppingDate = as.Date("2020-04-01")) {
  
  cumulData <- rawData
  cumulData$Date <- ymd(cumulData$Date)

  cumulData <- cumulData[cumulData$Date <= stoppingDate, ]
  cumulData <- cbind(Date=cumulData$Date, as.data.frame(apply(cumulData[,-1, drop=F], 2 , function(x) {fillInMissingCumulativeData(cumulData$Date, x)})))
  
  incidenceData <- as.data.frame(apply(cumulData[,-1, drop=F], 2, function(x) {  incidence <- x - c(0, x[1:(length(x)-1)]) ; return(incidence)}))
  incidenceData <- cbind(Date=cumulData$Date, incidenceData)
  incidenceData <- melt(incidenceData, id.vars="Date")
  colnames(incidenceData) <- c("date", "region", "value")
  incidenceData$data_type <- dataType
  incidenceData$value_type <- "incidence"
  incidenceData$estimate_type <- NA
  
  cumulData <- melt(cumulData, id.vars="Date")
  colnames(cumulData) <- c("date", "region", "value")
  cumulData$data_type <- dataType
  cumulData$value_type <- "cumul"
  cumulData$estimate_type <- NA
  
  return(rbind(cumulData, incidenceData))
}

## Fetch data from openZH via Daniel Probst's repo
getSwissDataFromOpenZH <- function(stopAfter = as.Date("2020-04-01")) {
  
  countTypes <- list("confirmed", "deaths")
  typeLabels <- list("cases", "fatalities")
  # countTypes <- list("confirmed")
  # typeLabels <- list("cases")
  names(countTypes) <- typeLabels
  names(typeLabels) <- countTypes
  
  baseUrl <-  "https://raw.githubusercontent.com/daenuprobst/covid19-cases-switzerland/master/"
  
  data <- data.frame(date=c(), region=c(), value=c(), data_type=c(), value_type=c(), estimate_type=c())
  
  for(typeLabel in typeLabels) {
    
    cumulFileUrl <- paste0(baseUrl, "covid19_",typeLabel,"_switzerland_openzh.csv")
    cumulData <- read.csv(cumulFileUrl)
    data <- rbind(data, meltCumulativeData(cumulData,  countTypes[[typeLabel]], stoppingDate = stopAfter))
  }
  
  return(data)
}

## Include hospitalization counts from local csv files
getHospitalData <- function(region="BS", basePathToCSV="../data/Hospital_cases_") {
  filePath <- paste0(basePathToCSV, region, ".csv")
  cumData <- read_csv(filePath)
  cumData <- cumData[,c(1,3)]
  return(meltCumulativeData(cumData, "hospitalized_FH"))
}

## Combine openZH data with hospitalization data
getAllSwissData <- function(stoppingAfter = as.Date("2020-04-01")){
  openZHData <- getSwissDataFromOpenZH(stopAfter=stoppingAfter)
  hospitalData <- rbind(getHospitalData("BS"),
                        getHospitalData("BL"))
  
  return(rbind(openZHData, hospitalData))
}

### Apply EpiEstim R estimation method to 'incidenceData' timeseries with 'dates' the dates associated
##
## 'estimateOffsetting' is the number of days the estimates are to be shifted towards the past (to account for delay between infection and testing/hospitalization/death..)
## 'ledtTruncation' is the number of days of estimates that should be ignored at the start of the time series
## 'method' takes value either 'Cori' or  'WallingaTeunis'. 'Cori' is the classic EpiEstim R(t) method, 'WallingaTeunis' is the method by Wallinga and Teunis (also implemented in EpiEstim)
## 'minimumCumul' is the minimum cumulative count the incidence data needs to reach before the first Re estimate is attempted (if too low, EpiEstim can crash)
## 'windowLength' is the size of the sliding window used in EpiEstim
## 'mean_si' and 'std_si' are the mean and SD of the serial interval distribution used by EpiEstim
estimateRe <- function(dates, incidenceData, estimateOffsetting = 10, rightTruncation=0, leftTruncation = 5, method="Cori", minimumCumul = 5, windowLength= 4, mean_si = 4.8, std_si  =2.3) {
  
  ## First, remove missing data at beginning of series
  while(length(incidenceData) > 0 & is.na(incidenceData[1])) {
    incidenceData <- incidenceData[-1]
    dates <- dates[-1]
    if(length(incidenceData) == 0) {
      return(data.frame(date=c(), value_type=c(), value=c(), estimate_type=c()))
    }
  }
  
  ## Then, remove missing data at the end of the series
  while(length(incidenceData) > 0 & is.na(incidenceData[length(incidenceData)])) {
    incidenceData <- incidenceData[-length(incidenceData)]
    dates <- dates[-length(dates)]
    if(length(incidenceData) == 0) {
      return(data.frame(date=c(), value_type=c(), value=c(), estimate_type=c()))
    }
    
  }
  
  ## Replace missing data in rest of series by zeroes (required for using EpiEstim)
  incidenceData[is.na(incidenceData)] <- 0
  
  offset <- 1
  cumulativeIncidence <- 0
  while(cumulativeIncidence < minimumCumul) {
    if(offset > length(incidenceData)) {
      return(data.frame(date=c(), value_type=c(), value=c(), estimate_type=c()))
    }
    cumulativeIncidence <- cumulativeIncidence + incidenceData[offset]
    offset <- offset + 1
  }
  
  ## offset needs to be at least two for EpiEstim
  offset <- max(2, offset)
  
  rightBound <- length(incidenceData)- (windowLength -1)
  
  if(rightBound < offset) { ## no valid data point, return empty estimate
    return(data.frame(date=c(), value_type=c(), value=c(), estimate_type=c()))
  }
  
  ## generate start and end bounds for Re estimates
  t_start <- seq(offset, rightBound)
  t_end <- t_start + windowLength -1
  
  if(method == "Cori") {
    
    R_instantaneous <- estimate_R(incidenceData, 
                                  method="parametric_si", 
                                  config = make_config(list(
                                    mean_si = mean_si, std_si = std_si,
                                    t_start = t_start,
                                    t_end = t_end)))
    
  } else if(method == "WallingaTeunis") {
    
    R_instantaneous <- wallinga_teunis(incidenceData,
                                       method="parametric_si",
                                       config = list(
                                         mean_si = mean_si, std_si = std_si,
                                         t_start = t_start,
                                         t_end = t_end,
                                         n_sim = 100))
  } else {
    print("Unknown estimation method")
    return(data.frame(date=c(), value_type=c(), value=c(), estimate_type=c()))
  }
  
  outputDates <- dates[t_end]
  ## offset dates to account for delay between infection and recorded event (testing, hospitalization, death...)
  outputDates <- outputDates - estimateOffsetting
  
  R_mean <- R_instantaneous$R$`Mean(R)`
  R_highHPD <- R_instantaneous$R$`Quantile.0.975(R)`
  R_lowHPD <- R_instantaneous$R$`Quantile.0.025(R)`
  
  if(rightTruncation > 0) {
    
    if(rightTruncation >= length(outputDates)) {
      return(data.frame(date=c(), value_type=c(), value=c(), estimate_type=c()))
    }
    
    originalLength <- length(outputDates)
    outputDates <- outputDates[-seq(originalLength, by=-1, length.out=rightTruncation)]
    R_mean <- R_mean[-seq(originalLength, by=-1, length.out=rightTruncation)]
    R_highHPD <- R_highHPD[-seq(originalLength, by=-1, length.out=rightTruncation)]
    R_lowHPD <- R_lowHPD[-seq(originalLength, by=-1, length.out=rightTruncation)]
    
  }
  
  if (leftTruncation > 0) {

    if(leftTruncation >= length(outputDates)) {
      return(data.frame(date=c(), value_type=c(), value=c(), estimate_type=c()))
    }
    originalLength <- length(outputDates)
    outputDates <- outputDates[-seq(1, leftTruncation)]
    R_mean <- R_mean[-seq(1, leftTruncation)]
    R_highHPD <- R_highHPD[-seq(1, leftTruncation)]
    R_lowHPD <- R_lowHPD[-seq(1, leftTruncation)]
  }
  
  result <- data.frame(date=outputDates,
                       R_mean=R_mean, 
                       R_highHPD=R_highHPD,
                       R_lowHPD=R_lowHPD)
  
  result <- melt(result, id.vars="date")
  colnames(result) <- c("date", "value_type", "value")
  result$estimate_type <- method
  
  return(result)
}

## Perform R(t) estimations with EpiEstim on each 'region' of the data, with each 'method' and on each 'data_type'
## 'region' is the geographical region
## 'data_type' can be 'confirmed' for confirmed cases, 'deaths' for fatalities, 'hospitalized_FH' for hospitalization data directly from hospitals (not via openZH here)
doAllReEstimations <- function(data, slidingWindow=3 ,methods=c("Cori", "WallingaTeunis")) {
  
  ## Input number of days estimates should be offset for each data type and each estimation method
  ## For instance, estimates based on confirmed cases are shifted to the past by 10 days for 'Cori' estimates and by 5 days for Wallinga-Teunis estimates
  delaysCori <- c(10, 20, 8) 
  names(delaysCori) <- c("confirmed", "deaths", "hospitalized_FH")
  delaysWT <- c(5, 15, 3) 
  names(delaysWT) <- c("confirmed", "deaths", "hospitalized_FH")
  
  fullResults <- data.frame(date=c(), region=c(), value=c(),data_type=c(), value_type=c(), estimate_type=c())
  
  # do the Re estimations for each region, each type of data, and each Re estimation method
  for(region_i in unique(data$region)) {
    subset_data_region <- subset(data, region == region_i)
    for(data_type_i in unique(subset_data_region$data_type)) {
      subset_data <- subset(subset_data_region, data_type == data_type_i)
      for(method_i in methods) {
        incidence_data <- subset_data$value[subset_data$value_type == "incidence"]
        dates <- subset_data$date[subset_data$value_type == "incidence"]
        if(method_i == "Cori") {
          
          offsetting <- delaysCori[data_type_i]
          result <- estimateRe(dates=dates, incidenceData=incidence_data, windowLength =  slidingWindow, estimateOffsetting = offsetting, rightTruncation = 0, leftTruncation=5, method=method_i)
        } else if(method_i == "WallingaTeunis") {
          
          offsetting <- delaysWT[data_type_i]
          result <- estimateRe(dates=dates, incidenceData=incidence_data, windowLength = slidingWindow, estimateOffsetting = offsetting, rightTruncation = 8, leftTruncation=0, method=method_i)
        }
        if(nrow(result) > 0) {
          result$region <- region_i
          result$data_type <- data_type_i
          ## need to reorder columns in 'results' dataframe to do the same as in data
          result <- result[,c(1,5,3,6,2,4)]
          fullResults <- rbind(fullResults, result)
        }
      }
    }
  }
  return(rbind(data, fullResults))
}



### Plotting functions
makePlotFigure2 <- function(meltData, dataType="confirmed", windowLength=3) {
  
  meltData <- subset(meltData, meltData$data_type == dataType)
  castData <- cast(meltData)
  castData$estimated <- !is.na(castData$estimate_type)
  
  ### Ten of the eleven cantons with highest absolute numbers of cases, excluding Graubünden because sparse data in that case.
  dataCases <- subset(castData, castData$estimated==F & castData$region %in% c("VD", "GE", "TI", "ZH", "VS", "BE", "BS", "BL", "AG","FR", "CH"))
  estimates <- subset(castData, castData$estimated==T & castData$region %in% c("VD", "GE", "TI", "ZH", "VS", "BE", "BS", "BL", "AG","FR", "CH"))
  
  pCases <- ggplot(dataCases, aes(x=date)) + 
    facet_grid(region ~.) +
    geom_line(aes(y = cumul), color = "black") + 
    geom_bar(aes(y = incidence), color = "black", stat = "identity", width=0.5) + 
    scale_x_date(date_breaks = "3 days", 
                 date_labels = '%b\n%d',
                 limits = c(as.Date("2020-02-26"), as.Date("2020-04-01"))) + 
    scale_y_log10() + 
    ylab("Cumulative (line) and daily (bars) number of confirmed cases") + 
    xlab("") +
    theme_bw() + 
    theme(
      strip.background = element_blank(),
      strip.text.y = element_blank(),
      axis.text.y= element_text(size=12),
      axis.text.x= element_text(size=11),
      axis.title.y =  element_text(size=17)
    )
  
  pRe <- ggplot(estimates, aes(x=date)) + 
    facet_grid(region ~.) +
    geom_ribbon(aes(ymin=R_lowHPD,ymax=R_highHPD, group=estimate_type, color=estimate_type, fill=estimate_type),alpha=0.3) + 
    geom_line(aes(y = R_mean, group=estimate_type, color=estimate_type)) +
    geom_hline(yintercept = 1, linetype="dashed") + 
    geom_vline(xintercept = c(as.Date("2020-03-14"), as.Date("2020-03-17"), as.Date("2020-03-20")), linetype="dotted") + 
    geom_vline(xintercept = c(as.Date("2020-03-07")), linetype="dashed") + 
    annotate("rect", xmin=as.Date("2020-03-14"), xmax=as.Date("2020-03-17"), ymin=-1, ymax=Inf, alpha=0.45, fill="grey") + 
    scale_x_date(date_breaks = "2 days", 
                 date_labels = '%b\n%d',
                 limits = c(as.Date("2020-03-06"), as.Date("2020-03-21"))) + 
    coord_cartesian(ylim=c(0,4)) +
    # scale_y_continuous(limits = c(0, maxYscale)) +
    xlab("") + 
    ylab("Reproduction number") + 
    scale_colour_discrete(name  ="Method",
                          breaks=c("Cori", "WallingaTeunis"),
                          labels = expression(R(t), R[c](t))) +
    scale_fill_discrete(name  ="Method",
                        breaks=c("Cori", "WallingaTeunis"),
                        labels = expression(R(t), R[c](t))) +
    theme_bw() + 
    theme(
      strip.background = element_blank(),
      strip.text.y = element_text(size=16),
      axis.text.y= element_text(size=12),
      axis.text.x= element_text(size=11),
      axis.title.y =  element_text(size=17),
      legend.title = element_text(size=14),
      legend.text = element_text(size=12)
    )
  
  ggarrange(pCases, pRe, labels = c("A", "B"),
            font.label = list(size = 18),
            common.legend = TRUE, legend = "right")
  plotPath <- paste0("../plots/Fig2_Cases_Re_", windowLength, "_day_window_", gsub("-","", Sys.Date()), ".png")
  ggsave(plotPath, width = 28, height = 40, units = "cm")
}

makePlotFigure3 <- function(meltData, windowLength=3) {
  
  dateLimit <- as.Date("2020-03-31")
  
  castData <- cast(meltData)
  castData <- castData[castData$date <= dateLimit,  ]
  castData <- castData[castData$region %in% c("BS", "BL", "CH"),] # restrict to 3 regions of interest
  castData$region <-factor(castData$region, levels(droplevels(castData$region)))
  castData <- castData[!(castData$region %in% c("BS", "BL") & castData$data_type=="deaths"),] #  remove estimates and death counts for Basel cantons
  
  castDataCounts <- castData[is.na(castData$estimate_type),]
  castDataCounts$data_type <- factor(castDataCounts$data_type, levels=c( "confirmed", "deaths", "hospitalized_FH"))
  
  castDataEstimate <- castData[!is.na(castData$estimate_type) & castData$estimate_type == "Cori",] # restrict to Cori estimates
  castDataEstimate$data_type <- factor(castDataEstimate$data_type, levels=c("deaths", "hospitalized_FH", "confirmed"))
  
  
  pCases <- ggplot(castDataCounts, aes(x=date)) +
    facet_grid(region ~.) +
    geom_bar(aes(y = incidence,fill=data_type), stat = "identity", position=position_dodge(preserve="single"), width=1, alpha=0.8) +
    scale_x_date(date_breaks = "4 days", 
                   date_labels = '%b\n%d',
                   limits=c(as.Date("2020-03-01"), as.Date("2020-04-01"))) +
  
    geom_line(aes(y = cumul, group=data_type, color=data_type), size=1.2) + 
    scale_y_log10(breaks=c(1,10,100, 1000,10000, 100000, 1000000),
                  labels=c(1,10,100, 1000,10000, 100000, 1000000)) + 
    scale_colour_manual(values=gg_color(3)[c(3,1,2)],
                        labels=c("Confirmed cases", "Hospitalizations", "Deaths"),
                        breaks=c("confirmed", "hospitalized_FH", "deaths"),
                        name  ="Data source", 
                        aesthetics = c("colour", "fill")) +
    ylab("Cumulative (line) and daily (bars) numbers") + 
    xlab("") +
    theme_bw() + 
    theme(
      strip.background = element_blank(),
      strip.text.y = element_blank(),
      axis.text.y= element_text(size=13),
      axis.text.x= element_text(size=13),
      axis.title.y =  element_text(size=17),
      legend.title = element_text(size=14),
      legend.text = element_text(size=12)
    )
  
  testingChangeDate <- data.frame(region=c("BL","BS", "CH"), dateIntervention=c(as.Date("2020-03-16"),as.Date("2020-03-07"),as.Date("2020-03-07")))
  
  pRe <- ggplot(data=castDataEstimate, aes(x=date)) +
    facet_grid(region ~.) +
    geom_ribbon(aes(ymin=R_lowHPD,ymax=R_highHPD, fill=data_type, colour=data_type),alpha=0.5) +
    geom_line(aes(y=R_mean,group=data_type, color=data_type), size=1) + 
    geom_hline(yintercept = 1, linetype="dashed") + 
    geom_vline(xintercept = c(as.Date("2020-03-14"), as.Date("2020-03-17"), as.Date("2020-03-20")),
               linetype="dotted",
               size=0.8) + 
    annotate("rect", xmin=as.Date("2020-03-14"), xmax=as.Date("2020-03-17"), ymin=-1, ymax=Inf, alpha=0.45, fill="grey") + 
    geom_vline(data=testingChangeDate, aes(xintercept = dateIntervention), linetype="dashed", size=0.8) + 
    scale_x_date(date_breaks = "2 days",
                 date_labels = '%b\n%d',
                 limits=c(as.Date("2020-03-06"), as.Date("2020-03-21"))) +
    coord_cartesian(ylim=c(0,4)) +
    scale_colour_manual(values=gg_color(3)[c(1,2,3)],
                        labels=c("Confirmed cases", "Hospitalizations", "Deaths"),
                        breaks=c("confirmed", "hospitalized_FH", "deaths"),
                        name  ="Data source", 
                        aesthetics = c("colour", "fill")) +
    ylab("Re") +
    xlab("") +
    theme_bw() +
    theme(
      strip.background = element_blank(),
      strip.text.y = element_text(size=16),
      axis.text.y= element_text(size=13),
      axis.text.x= element_text(size=13),
      axis.title.y =  element_text(size=17),
      legend.title = element_text(size=14),
      legend.text = element_text(size=12))
  
  ggarrange(pCases, pRe, labels = c("A", "B"),
            font.label = list(size = 18),
            common.legend = TRUE, legend = "right")
  plotPath <- paste0("../plots/Fig3_Compare_Cases_Re_", windowLength, "_day_window.png")
  ggsave(plotPath, width = 28, height = 20, units = "cm")
}

### Make plot updated daily on "https://bsse.ethz.ch/cevo/research/sars-cov-2/real-time-monitoring-in-switzerland.html"
makePlotCumulativeAndDailyCasesAndRe <- function(meltData, windowLength=3) {
  
  meltData <- subset(meltData, meltData$data_type == "confirmed")
  castData <- cast(meltData)
  castData$estimated <- !is.na(castData$estimate_type)
  
  ### Ten of the eleven cantons with highest absolute numbers of cases, excluding Graubünden because sparse data in that case.
  dataCases <- subset(castData, castData$estimated==F & castData$region %in% c("VD", "GE", "TI", "ZH", "VS", "BE", "BS", "BL", "AG","FR", "CH"))
  estimates <- subset(castData, castData$estimated==T & castData$estimate_type=="Cori" & castData$region %in% c("VD", "GE", "TI", "ZH", "VS", "BE", "BS", "BL", "AG","FR", "CH"))

  pCases <- ggplot(dataCases, aes(x=date)) + 
    facet_grid(region ~.) +
    geom_line(aes(y = cumul), color = "black") + 
    geom_bar(aes(y = incidence), color = "black", stat = "identity", width=0.5) + 
    scale_x_date(date_breaks = "3 days", 
                 date_labels = '%b\n%d',
                 limits = c(as.Date("2020-02-25"), Sys.Date()+1)) +
    scale_y_log10() + 
    ylab("Cumulative (line) and daily (bars)\nnumber of confirmed cases") + 
    xlab("") +
    theme_bw() + 
    theme(
      strip.background = element_blank(),
      strip.text.y = element_blank(),
      axis.text.y= element_text(size=12),
      axis.text.x= element_text(size=11),
      axis.title.y =  element_text(size=17)
      # axis.title.y =  element_text(size=11)
    )
  
  pRe <- ggplot(estimates, aes(x=date)) + 
    facet_grid(region ~.) +
    geom_ribbon(aes(ymin=R_lowHPD,ymax=R_highHPD),alpha=0.3) + 
    geom_line(aes(y = R_mean)) +
    geom_hline(yintercept = 1, linetype="dashed") + 
    scale_x_date(date_breaks = "2 days", 
                 date_labels = '%b\n%d',
                 limits = c(as.Date("2020-03-01"), Sys.Date()-10)) + 
    coord_cartesian(ylim=c(0,4)) +
    geom_vline(xintercept = c(as.Date("2020-02-28"),as.Date("2020-03-06"), as.Date("2020-03-14"), as.Date("2020-03-17"), as.Date("2020-03-20")), linetype="dotted") + 
    annotate("rect", xmin=as.Date("2020-03-14"), xmax=as.Date("2020-03-17"), ymin=-1, ymax=Inf, alpha=0.45, fill="grey") + 
    xlab("") + 
    ylab("Reproduction number") + 
    theme_bw() + 
    theme(
      strip.background = element_blank(),
      strip.text.y = element_text(size=16),
      axis.text.y= element_text(size=12),
      axis.text.x= element_text(size=11),
      axis.title.y =  element_text(size=17),
      # axis.title.y =  element_text(size=11),
      legend.title = element_text(size=14),
      legend.text = element_text(size=12)
    )
  
  ggarrange(pCases, pRe)
  plotPath <- paste0("../plots/Re_CH_", gsub("-","", Sys.Date()), ".png")
  ggsave(plotPath, width = 28, height = 45, units = "cm")
}



#################################
#### Start of the script ########
#################################


## Set size of sliding window
window <- 3
### Get data
raw_data <- getAllSwissData(stoppingAfter = as.Date("2020-04-01"))
### Run EpiEstim
data <- doAllReEstimations(raw_data, slidingWindow=window)

### rename data columns to make plotting easier
colnames(data) <- c("date" ,"region", "value" ,"data_type", "variable", "estimate_type")

### make plot for website
makePlotCumulativeAndDailyCasesAndRe(data, windowLength= window)

### make manuscript figures
makePlotFigure2(data, windowLength=window)
makePlotFigure3(data, windowLength=window)
