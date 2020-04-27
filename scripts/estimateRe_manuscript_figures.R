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
library(plyr)

### Help function for plotting
gg_color <- function(n) {
  
  hues = seq(15, 375, length = n + 1)
  
  hcl(h = hues, l = 65, c = 100)[1:n]
  
}


#### Build empirical CDF from draws summing samples from two gamma distributions
make_empirical_cdf <- function(shape, scale, numberOfSamples=1E6) {
  draws <- round(rgamma(numberOfSamples, shape=shape[1], scale=scale[1]) + rgamma(numberOfSamples, shape=shape[2], scale=scale[2]) )
  return(Vectorize(ecdf(draws)))
}

### Function made to account for missing entries in data
## 
## Makes linear interpolation of missing values
## 
## For dates after 'startDate' if two consecutive reports of cumulative cases are equal, replaces the second one by an interpolation with the entry from the previous and next day
## This is done to account for days when the confirmed case data was not updated.
## It does not work if the data was not updated more than 2 days in a row.
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
meltCumulativeData <- function(rawData, dataType, fillInMissingData=F, stoppingDate = (Sys.Date() -1)) {
  
  cumulData <- rawData
  cumulData$Date <- ymd(cumulData$Date)
  
  cumulData <- cumulData[cumulData$Date <= stoppingDate, ]
  
  
  if(fillInMissingData == T) { ### fill in missing incidence data
    cumulData <-cbind(Date=cumulData$Date, as.data.frame(apply(cumulData[,-1, drop=F], 2 , function(x) {fillInMissingCumulativeData(cumulData$Date, x)})))
  }
  
  
  incidenceData <- as.data.frame(apply(cumulData[,-1, drop=F], 2, function(x) {  incidence <- x - c(0, x[1:(length(x)-1)]) ; return(incidence)}))
  incidenceData <- cbind(Date=cumulData$Date, incidenceData)
  incidenceData <- melt(incidenceData, id.vars="Date")
  colnames(incidenceData) <- c("date", "region", "value")
  incidenceData$data_type <- dataType
  incidenceData$variable <- "incidence"
  incidenceData$estimate_type <- NA
  incidenceData$replicate <- NA
  
  
  # only done for plotting, but not applied to incidence data
  if(fillInMissingData == F) {
    cumulData <-cbind(Date=cumulData$Date, as.data.frame(apply(cumulData[,-1, drop=F], 2 , function(x) {fillInMissingCumulativeData(cumulData$Date, x)})))
  }
  
  cumulData <- melt(cumulData, id.vars="Date")
  colnames(cumulData) <- c("date", "region", "value")
  cumulData$data_type <- dataType
  cumulData$variable <- "cumul"
  cumulData$estimate_type <- NA
  cumulData$replicate <- NA
  
  return(rbind(cumulData, incidenceData))
}

## Fetch data from openZH via Daniel Probst's repo
getSwissDataFromOpenZH <- function(stopAfter = (Sys.Date() -1)) {
  
  countTypes <- list("confirmed", "deaths")
  typeLabels <- list("cases", "fatalities")

  names(countTypes) <- typeLabels
  names(typeLabels) <- countTypes
  
  baseUrl <-  "https://raw.githubusercontent.com/daenuprobst/covid19-cases-switzerland/master/"
  
  data <- data.frame(date=c(), region=c(), value=c(), data_type=c(), variable=c(), estimate_type=c())
  
  for(typeLabel in typeLabels) {
    
    cumulFileUrl <- paste0(baseUrl, "covid19_",typeLabel,"_switzerland_openzh.csv")
    # cumulFileUrl <- "/Users/scirej/Documents/nCov19/Incidence_analysis/data/openZH_daenuprobst/covid19_cases_switzerland_openzh.csv" # Fix while raw.github is down 
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
  return(meltCumulativeData(cumData, "hospitalized"))
}

## Combine openZH data with hospitalization data
getAllSwissData <- function(stoppingAfter = (Sys.Date() -1)){
  openZHData <- getSwissDataFromOpenZH(stopAfter=stoppingAfter)
  hospitalData <- rbind(getHospitalData("BS"),
                        getHospitalData("BL"))
  
  return(rbind(openZHData, hospitalData))
}


#### Randomly sample infection dates from the incidence timeseries using two gamma distributions
#### One gamma-distributed waiting time is the incubation period
#### The second one is the period between symptom onset and report (of positive test, death, hospitalization...)
#### For each incidence time series 'numberOfReplicates' replicates are drawn
#### 'region_i' is the region of the data in 'data_subset'
#### 'data_type_i' is its data type ("confirmed" for positive test report, "death" for fatality report...)
drawInfectionDates <- function(data_subset, region_i, data_type_i, numberOfReplicates=100, shapeIncubation, scaleIncubation, shapeOnsetToCount,scaleOnsetToCount) {
  
  
  ### Obtain a pdf for the sum of the gamma distributions for incubation and delay from symptoms onset to count
  Fhat <- make_empirical_cdf(shape=c(shapeIncubation, shapeOnsetToCount), scale=c(scaleIncubation, scaleOnsetToCount))
  
  ### Initialize variables 
  lastInfectionDate <- as.Date("1900-01-01") # start with low date
  partial_results <- list()
  
  
  for(replicateNum in 1:numberOfReplicates){
    
    infectionDates <- c()
    for(dateTest in data_subset$date) {
      
      ## for each date in the time series, if incidence on that day is > 0
      ## draw 'incidenceOnDay' delays between infection and count, with 'incidenceOnDay' the daily incidence
      
      incidenceOnDay <- data_subset$value[data_subset$date == dateTest]
      
      if(!is.na(incidenceOnDay) & incidenceOnDay > 0) {
        sampledInfectionToCountDelay <- round(rgamma(incidenceOnDay, shape=shapeOnsetToCount, scale=scaleOnsetToCount) + rgamma(incidenceOnDay, shape=shapeIncubation, scale=scaleIncubation) )
        
        drawnInfectionTimes <- dateTest - sampledInfectionToCountDelay 
        infectionDates <- c(infectionDates, drawnInfectionTimes)
      }
    }
    
    if(length(infectionDates) == 0){
      return(data.frame())
    }

    infectionDates <- as_date(infectionDates)
    
    ### keep track of the most recent date an infection has been sampled, across all replicates
    lastInfectionDate <- max(lastInfectionDate, max(infectionDates))
    
    ### build a vector of consecutive dates between first and last day an infection was sampled
    allInfectionDates <- seq(min(infectionDates), max(infectionDates), by="days")
    
    lastDayTesting <- max(data_subset$date)
    infectionCount <- c()
    trueInfectionCount <- c()
    
    ### account for the yet-to-be-sampled infections happening on each day
    ### the closer to the present, the more likely it is that an infection has not been reported yet.
    for(i in 1:length(allInfectionDates)) {
      infectionCount[i] <- sum(infectionDates == allInfectionDates[i])
      windowToReport <- as.numeric(lastDayTesting - allInfectionDates[i])
      
      ## Fhat(windowToReport) is the probability that an infection is sampled before 'windowToReport' days
      trueInfectionCount[i] <- round(infectionCount[i] * 1/Fhat(windowToReport)) 
    }
    
    results <- list(date=allInfectionDates, infections=trueInfectionCount)
    
    partial_results <- c( partial_results, list(results))
    
  }
  
  ## Now we need to extend the time series so that they all end on the same day.
  ## Thus we need to add trailing zeroes to the true infection counts that end earlier
  results_list <- list()
  
  for(replicateNum in 1:numberOfReplicates){
    
    infectionDates <-   partial_results[[replicateNum]]$date
    infectionTimeSeries <- partial_results[[replicateNum]]$infections
    lastDayWithSamples <- max(infectionDates)
    
    
    if(lastDayWithSamples < lastInfectionDate) {
      infectionDates <- c(infectionDates, seq(lastDayWithSamples + 1, lastInfectionDate, by="days"))
      infectionTimeSeries <- c(infectionTimeSeries, rep(0, lastInfectionDate - lastDayWithSamples ))
    }
    
    
    #### prepare dataframe for this particular replicate before combining all replicates in a single dataframe
    region <- rep(region_i, length(infectionDates))
    
    data_type_name <- rep(paste0("infection_", data_type_i), length(infectionDates))
    variable <- rep("incidence", length(infectionDates))
    estimate_type <- rep(NA, length(infectionDates))
    replicate <- rep(replicateNum, length(infectionDates))
    
    infectionsDF <- data.frame(date=infectionDates,
                               region=region, 
                               value=infectionTimeSeries,
                               data_type=data_type_name,
                               variable=variable,
                               estimate_type=estimate_type,
                               replicate=replicate,
                               stringsAsFactors = F)
    
    results_list <- c(results_list, list(infectionsDF))
  }
  
  return(rbind.fill(results_list))
}


#### Apply drawInfectionDates to the entire dataset
drawAllInfectionDates <- function(data, source_data="confirmed", numberOfReplicates=100 , meanIncubation, sdIncubation, meanOnsetToCount, sdOnsetToCount) {

  ### gamma distribution parameters for incubation period
  shapeIncubation <- meanIncubation^2/(sdIncubation^2)
  scaleIncubation <- (sdIncubation^2)/meanIncubation
  
  ### parameters for gamma distribution between symptom onset and report
  shapeOnsetToCount <- meanOnsetToCount^2/(sdOnsetToCount^2)
  scaleOnsetToCount <- (sdOnsetToCount^2)/meanOnsetToCount
  
  results <- list()
  
  for(count_type_i in source_data) {
    
    results_list <- lapply(unique(data$region), 
                           function(x){
                             subset_data <- subset(data, region==x & data_type == count_type_i & variable=="incidence");
                             
                             if(nrow(subset_data) == 0) {return(data.frame())}
                             
                             drawInfectionDates(subset_data, x, count_type_i, numberOfReplicates, 
                                                shapeIncubation, scaleIncubation, shapeOnsetToCount[[count_type_i]], scaleOnsetToCount[[count_type_i]]) 
                             
                           })
    results <- c(results, results_list)
  }
  
  return(rbind.fill(c(list(data), results)))
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
      return(data.frame(date=c(), variable=c(), value=c(), estimate_type=c()))
    }
  }
  
  ## Then, remove missing data at the end of the series
  while(length(incidenceData) > 0 & is.na(incidenceData[length(incidenceData)])) {
    incidenceData <- incidenceData[-length(incidenceData)]
    dates <- dates[-length(dates)]
    if(length(incidenceData) == 0) {
      return(data.frame(date=c(), variable=c(), value=c(), estimate_type=c()))
    }
    
  }
  
  ## Replace missing data in rest of series by zeroes (required for using EpiEstim)
  incidenceData[is.na(incidenceData)] <- 0
  
  offset <- 1
  cumulativeIncidence <- 0
  while(cumulativeIncidence < minimumCumul) {
    if(offset > length(incidenceData)) {
      return(data.frame(date=c(), variable=c(), value=c(), estimate_type=c()))
    }
    cumulativeIncidence <- cumulativeIncidence + incidenceData[offset]
    offset <- offset + 1
  }
  
  ## offset needs to be at least two for EpiEstim
  offset <- max(2, offset)
  
  rightBound <- length(incidenceData)- (windowLength -1)
  
  if(rightBound < offset) { ## no valid data point, return empty estimate
    return(data.frame(date=c(), variable=c(), value=c(), estimate_type=c()))
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
                                         n_sim = 10))
  } else {
    print("Unknown estimation method")
    return(data.frame(date=c(), variable=c(), value=c(), estimate_type=c()))
  }
  
  outputDates <- dates[t_end]
  ## offset dates to account for delay between infection and recorded event (testing, hospitalization, death...)
  outputDates <- outputDates - estimateOffsetting
  
  R_mean <- R_instantaneous$R$`Mean(R)`
  R_highHPD <- R_instantaneous$R$`Quantile.0.975(R)`
  R_lowHPD <- R_instantaneous$R$`Quantile.0.025(R)`
  
  if(rightTruncation > 0) {
    
    if(rightTruncation >= length(outputDates)) {
      return(data.frame(date=c(), variable=c(), value=c(), estimate_type=c()))
    }
    
    originalLength <- length(outputDates)
    outputDates <- outputDates[-seq(originalLength, by=-1, length.out=rightTruncation)]
    R_mean <- R_mean[-seq(originalLength, by=-1, length.out=rightTruncation)]
    R_highHPD <- R_highHPD[-seq(originalLength, by=-1, length.out=rightTruncation)]
    R_lowHPD <- R_lowHPD[-seq(originalLength, by=-1, length.out=rightTruncation)]
    
  }
  
  if (leftTruncation > 0) {

    if(leftTruncation >= length(outputDates)) {
      return(data.frame(date=c(), variable=c(), value=c(), estimate_type=c()))
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
  colnames(result) <- c("date", "variable", "value")
  result$estimate_type <- method
  
  return(result)
}


doReEstimation <- function(data_subset, region_i, data_type_i,  replicateNum, slidingWindow, methods=c("Cori", "WallingaTeunis"), delays, truncations) {
  
  end_result <-  data.frame(date=c(), region=c(), value=c(),data_type=c(), variable=c(), estimate_type=c(), replicate=c())
  
  for(method_i in methods) {
    
    incidence_data <- data_subset$value[data_subset$variable == "incidence"]
    dates <- data_subset$date[data_subset$variable == "incidence"]
    
    offsetting <- delays[method_i]
    
    leftTrunc <- truncations$left[method_i]
    rightTrunc <- truncations$right[method_i]
    
    result <- estimateRe(dates=dates, incidenceData=incidence_data, windowLength =  slidingWindow, estimateOffsetting = offsetting, rightTruncation = rightTrunc, leftTruncation=leftTrunc, method=method_i)
    
    if(nrow(result) > 0) {
      
      result$region <- region_i
      result$data_type <- data_type_i
      result$replicate <- replicateNum
      ## need to reorder columns in 'results' dataframe to do the same as in data
      result <- result[,c(1,5,3,6,2,4,7)]
      
      end_result <- rbind(end_result ,result)
      
    }
  }
  
  return(end_result)
}

## Perform R(t) estimations with EpiEstim on each 'region' of the data, with each 'method' and on each 'data_type'
## 'region' is the geographical region
## 'data_type' can be 'confirmed' for confirmed cases, 'deaths' for fatalities, 'hospitalized' for hospitalization data directly from hospitals (not via openZH here)
doAllReEstimations <- function(data, slidingWindow=3 ,methods=c("Cori", "WallingaTeunis"), all_delays, truncations, piecewise_constant=F) {
  
  results_list <- list(data)
  
  for(region_i in unique(data$region)) {
    
    print(region_i)
    subset_data_region <- subset(data, region == region_i)
    
    for(data_type_i in unique(subset_data_region$data_type)) {
      
      print(data_type_i)
      subset_data <- subset(subset_data_region, data_type == data_type_i)
      
      delay_i <- all_delays[[data_type_i]]
      
      if(is.na(unique(subset_data$replicate))) {
        
        results_list <- c(results_list, list(doReEstimation(subset_data, region_i, data_type_i, replicateNum=0, slidingWindow=slidingWindow, delays=delay_i, truncations=truncations, methods=methods)))
        
  
        
      } else {
        
        for (replicate_i in unique(unique(subset_data$replicate))) {
          subset_data_rep <- subset(subset_data, subset_data$replicate == replicate_i)
          
          results_list <- c(results_list, list(doReEstimation(subset_data_rep, region_i, data_type_i, replicateNum=replicate_i, slidingWindow=slidingWindow, methods=methods, delays=delay_i, truncations=truncations)))
        }
        
      }
    }
  }
  return(rbind.fill(results_list))
  # return(rbind(data, fullResults))
}

### Plotting functions
makePlotFigure2 <- function(meltData) {
  
  meltData <- subset(meltData, data_type %in% c("infection_confirmed", "confirmed"))
  castData <- cast(meltData)
  castData$region <- factor(castData$region, levels=c("AG", "BE", "BL", "BS", "FR", "GE", "TI", "VD", "VS", "ZH", "CH"))
  castData$estimated <- !is.na(castData$estimate_type)
  
  ### Ten of the eleven cantons with highest absolute numbers of cases, excluding Graubünden because sparse data in that case.
  dataCases <- subset(castData, estimated==F & region %in% c("VD", "GE", "TI", "ZH", "VS", "BE", "BS", "BL", "AG","FR", "CH") & data_type == "confirmed")
  estimates <- subset(castData, estimated==T & region %in% c("VD", "GE", "TI", "ZH", "VS", "BE", "BS", "BL", "AG","FR", "CH") & data_type == "infection_confirmed" & !(estimate_type == "WallingaTeunis" & date > as.Date("2020-04-07")))
  
  estimates$median_R_mean <- with(estimates, ave(R_mean, date, region, data_type, estimate_type, FUN = median ))
  estimates$median_R_highHPD <- with(estimates, ave(R_highHPD, date, region, data_type, estimate_type, FUN = median ))
  estimates$median_R_lowHPD <- with(estimates, ave(R_lowHPD, date, region, data_type, estimate_type, FUN = median ))
  
  estimates$highQuantile_R_highHPD <- with(estimates, ave(R_highHPD, date, region, data_type, estimate_type, FUN = function(x) quantile(x, probs=0.975, na.rm=T) ))
  estimates$lowQuantile_R_lowHPD <- with(estimates, ave(R_lowHPD, date, region, data_type, estimate_type, FUN = function(x) quantile(x, probs=0.025, na.rm=T) ))
  
  
  pCases <- ggplot(dataCases, aes(x=date)) +
  # ggplot(dataCases, aes(x=date)) +
    facet_grid(region ~.) +
    geom_line(aes(y = cumul), color = "black") + 
    geom_bar(aes(y = incidence), color = "black", stat = "identity", width=0.5) + 
    scale_x_date(date_breaks = "5 days", 
                 date_labels = '%b\n%d',
                 limits = c(as.Date("2020-02-26"), as.Date("2020-04-22"))) + 
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
  # ggplot(estimates, aes(x=date)) + 
    facet_grid(region ~.) +
    geom_ribbon(aes(ymin=median_R_lowHPD,ymax=median_R_highHPD, group=estimate_type, fill=estimate_type),alpha=0.6, colour=NA) +
    geom_ribbon(aes(ymin=lowQuantile_R_lowHPD,ymax=highQuantile_R_highHPD, fill=estimate_type),alpha=0.3, colour=NA) +
    geom_line(aes(y = median_R_mean, group=estimate_type, color=estimate_type), size=1) +
    geom_hline(yintercept = 1, linetype="dashed") + 
    geom_vline(xintercept = c(as.Date("2020-03-14"), as.Date("2020-03-17"), as.Date("2020-03-20")), linetype="dotted") + 
    annotate("rect", xmin=as.Date("2020-03-14"), xmax=as.Date("2020-03-17"), ymin=-1, ymax=Inf, alpha=0.45, fill="grey") + 
    scale_x_date(date_breaks = "4 days", 
                 date_labels = '%b\n%d',
                 limits = c(as.Date("2020-03-07"), as.Date("2020-04-12"))) + 
    coord_cartesian(ylim=c(0,3.5)) +
    xlab("") + 
    ylab("Reproductive number") + 
    scale_colour_manual(values=c( "black", gg_color(3)[c(3)]),
                        labels = expression(R(t), R[c](t)),
                        breaks=c("Cori", "WallingaTeunis"),
                        name  ="Method",
                        aesthetics = c("fill", "color")) +
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
  plotPath <- paste0("../plots/Fig2_sampling_infect.png")
  ggsave(plotPath, width = 28, height = 40, units = "cm")
}

makePlotFigure3 <- function(meltData) {
  dateLimit <- as.Date("2020-03-31")
  
  castData <- cast(meltData)
  castData <- subset(castData, date <= dateLimit)
  castData$region <- factor(castData$region, levels=c("AG", "BE", "BL", "BS", "FR", "GE", "TI", "VD", "VS", "ZH", "CH"))
  castData$estimated <- !is.na(castData$estimate_type)
  
  ### Ten of the eleven cantons with highest absolute numbers of cases, excluding Graubünden because sparse data in that case.
  dataCases <- subset(castData, estimated==F & region %in% c("BS", "BL", "CH") & data_type %in% c("confirmed", "deaths", "hospitalized"))
  estimates <- subset(castData, estimated==T & region %in% c("BS", "BL", "CH") & data_type %in% c("infection_confirmed", "infection_deaths", "infection_hospitalized") & estimate_type == "Cori")
  
  dataCases$data_type <- factor(dataCases$data_type, levels=c("deaths", "hospitalized","confirmed"))
  estimates$data_type <- factor(estimates$data_type, levels=c("infection_deaths", "infection_hospitalized","infection_confirmed"))
  estimates$median_R_mean <- with(estimates, ave(R_mean, date, region, data_type, estimate_type, FUN = median ))
  estimates$median_R_highHPD <- with(estimates, ave(R_highHPD, date, region, data_type, estimate_type, FUN = median ))
  estimates$median_R_lowHPD <- with(estimates, ave(R_lowHPD, date, region, data_type, estimate_type, FUN = median ))
  
  estimates$highQuantile_R_highHPD <- with(estimates, ave(R_highHPD, date, region, data_type, estimate_type, FUN = function(x) quantile(x, probs=0.975, na.rm=T) ))
  estimates$lowQuantile_R_lowHPD <- with(estimates, ave(R_lowHPD, date, region, data_type, estimate_type, FUN = function(x) quantile(x, probs=0.025, na.rm=T) ))
  
  pCases <- ggplot(dataCases, aes(x=date)) +
    facet_grid(region ~.) +
    geom_bar(aes(y = incidence,fill=data_type), stat = "identity", position=position_dodge(preserve="single"), width=1, alpha=0.8) +
    scale_x_date(date_breaks = "4 days", 
                   date_labels = '%b\n%d',
                   limits=c(as.Date("2020-03-01"), as.Date("2020-04-01"))) +
  
    geom_line(aes(y = cumul, group=data_type, color=data_type), size=1.2) + 
    scale_y_log10() + 
    scale_colour_manual(values=c(gg_color(3)[c(1,3)], "black"),
                        labels=c("Confirmed cases", "Hospitalizations", "Deaths"),
                        breaks=c("confirmed", "hospitalized", "deaths"),
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
  
  # testingChangeDate <- data.frame(region=c("BL","BS", "CH"), dateIntervention=c(as.Date("2020-03-16"),as.Date("2020-03-07"),as.Date("2020-03-07")))
  testingChangeDate <- data.frame(region=c("BL"), dateIntervention=c(as.Date("2020-03-16")))
  
  pRe <- ggplot(estimates, aes(x=date)) +
    facet_grid(region ~.) +
    geom_ribbon(aes(ymin=median_R_lowHPD,ymax=median_R_highHPD, group=data_type, fill=data_type),alpha=0.6, colour=NA) +
    geom_ribbon(aes(ymin=lowQuantile_R_lowHPD,ymax=highQuantile_R_highHPD, fill=data_type),alpha=0.3, colour=NA) +
    geom_line(aes(y = median_R_mean, group=data_type, color=data_type), size=1) +
    geom_hline(yintercept = 1, linetype="dashed") +
    geom_vline(xintercept = c(as.Date("2020-03-14"), as.Date("2020-03-17"), as.Date("2020-03-20")),
               linetype="dotted",
               size=0.8) +
    annotate("rect", xmin=as.Date("2020-03-14"), xmax=as.Date("2020-03-17"), ymin=-1, ymax=Inf, alpha=0.45, fill="grey") +
    geom_vline(data=testingChangeDate, aes(xintercept = dateIntervention), linetype="dashed", size=0.8) +
    annotate("rect", xmin=as.Date("2020-03-14"), xmax=as.Date("2020-03-17"), ymin=-1, ymax=Inf, alpha=0.45, fill="grey") + 
    scale_x_date(date_breaks = "2 days", 
                 date_labels = '%b\n%d',
                 limits = c(as.Date("2020-03-07"), as.Date("2020-03-21"))) + 
    coord_cartesian(ylim=c(0,3.5)) +
    xlab("") + 
    ylab("Reproductive number") + 
    scale_colour_manual(values=c(gg_color(3)[c(1,3)], "black"),
                          labels=c("Confirmed cases", "Deaths", "Hospitalizations"),
                          breaks=c("infection_confirmed", "infection_deaths", "infection_hospitalized"),
                          name  ="Data source", 
                          aesthetics = c("colour", "fill")) +
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
  plotPath <- paste0("../plots/Fig3_sampled_infect.png")
  ggsave(plotPath, width = 28, height = 20, units = "cm")
}


#################################
#### Start of the script ########
#################################

# for incubation,  mean = 5.3, sd =3.2 (Linton et al., best gamma distr fit)
meanIncubation <- 5.3
sdIncubation <- 3.2

# for onset to test :data from BL canton
meanOnsetToTest <- 5.6
sdOnsetToTest <- 4.2

# for onset to hospitalization report : data from BL canton(14/04/20 update)
meanOnsetToHosp <- 6.6
sdOnsetToHosp <- 4.6

## for onset to death , mean =15.0 sd=6.9 (Linton et al. best gamma distr fit)
meanOnsetToDeath <- 15.0
sdOnsetToDeath <- 6.9

meanOnsetToCount <- c("confirmed"= meanOnsetToTest, "deaths"=meanOnsetToDeath, "hospitalized"=meanOnsetToHosp)
sdOnsetToCount <- c("confirmed"= sdOnsetToTest, "deaths"=sdOnsetToDeath, "hospitalized"=sdOnsetToHosp)


## Set size of sliding window
window <- 3

## Input
all_delays <- list(infection_confirmed=c(Cori=0, WallingaTeunis=-5),
                   infection_deaths=c(Cori=0, WallingaTeunis=-5),
                   infection_hospitalized=c(Cori=0, WallingaTeunis=-5),
                   confirmed=c(Cori=10, WallingaTeunis=5),
                   deaths=c(Cori=20, WallingaTeunis=15),
                   hospitalized=c(Cori=8, WallingaTeunis=3))

truncations <- list(left=c(Cori=5, WallingaTeunis=0),
                    right=c(Cori=0, WallingaTeunis=8))

replicates <- 100
### Get data
raw_data <- getAllSwissData(stoppingAfter = as.Date("2020-04-23"))

swissData <- subset(raw_data, region %in% c("VD", "GE", "TI", "ZH", "VS", "BE", "BS", "BL", "AG","FR", "CH") & !(region != "CH" & data_type %in% c("deaths")))
## need to fix script to allow for not subsetting like this (pb with some canton death timeseries)

drawnInfectTimesData <- drawAllInfectionDates(swissData, source_data=c("confirmed", "deaths", "hospitalized"), 
                                              numberOfReplicates = replicates, 
                                              meanIncubation = meanIncubation, sdIncubation = sdIncubation,
                                              meanOnsetToCount=meanOnsetToCount, sdOnsetToCount=sdOnsetToCount)

### Run EpiEstim
data <- doAllReEstimations(drawnInfectTimesData, slidingWindow=window,  all_delays=all_delays, truncations=truncations)

### make manuscript figures
makePlotFigure2(data)
makePlotFigure3(data)

