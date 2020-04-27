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
library("utils")

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
## Comment out getHospitalData line if  hospital data file is absent
getAllSwissData <- function(stoppingAfter = (Sys.Date() -1)){
  openZHData <- getSwissDataFromOpenZH(stopAfter=stoppingAfter)
  
  # hospitalData <- rbind(getHospitalData("BS"),
  #                       getHospitalData("BL"),
  #                       getHospitalData("CH"))
  
  hospitalData <- rbind(getHospitalData("CH")) 
  
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
estimateRe <- function(dates, incidenceData, estimateOffsetting = 10, rightTruncation=0, leftTruncation = 5, method="Cori", variationType= "slidingWindow", interval_ends= c("2020-03-13", "2020-03-16", "2020-03-20"), minimumCumul = 5, windowLength= 4, mean_si = 4.8, std_si  =2.3) {
  
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
  if(variationType == "step") {
    
    interval_end_indices <- sapply(interval_ends, function(x) {which(dates == as.Date(x))[1]})
    
    t_start <- c(offset, na.omit(interval_end_indices) + 1)
    t_end <- c(na.omit(interval_end_indices), length(incidenceData))
    
    if(offset >= length(incidenceData)) {
      return(data.frame(date=c(), variable=c(), value=c(), estimate_type=c()))
    }
    
    while(offset > t_end[1]) { 
      t_start <- t_start[-1]
      t_start[1] <- offset
      t_end <- t_end[-1]
    }
    
    outputDates <- dates[t_start[1]:t_end[length(t_end)]]
    
  } else if (variationType == "slidingWindow") {
    t_start <- seq(offset, rightBound)
    t_end <- t_start + windowLength -1
    
    outputDates <- dates[t_end]
  } else {
    print("Unknown time variation.")
    return(data.frame(date=c(), variable=c(), value=c(), estimate_type=c()))
  }
  
  ## offset dates to account for delay between infection and recorded event (testing, hospitalization, death...)
  outputDates <- outputDates - estimateOffsetting
  
  if(method == "Cori") {
    
    R_instantaneous <- estimate_R(incidenceData, 
                                  method="parametric_si", 
                                  config = make_config(list(
                                    mean_si = mean_si, 
                                    std_si = std_si,
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
  
  if(variationType == "step") {
    R_mean <- unlist(lapply(1:length(t_start), function(x) {rep(R_instantaneous$R$`Mean(R)`[x], t_end[x]-t_start[x]+1)}))
    R_highHPD <- unlist(lapply(1:length(t_start), function(x) {rep(R_instantaneous$R$`Quantile.0.975(R)`[x], t_end[x]-t_start[x]+1)}))
    R_lowHPD <- unlist(lapply(1:length(t_start), function(x) {rep(R_instantaneous$R$`Quantile.0.025(R)`[x], t_end[x]-t_start[x]+1)}))
  } else {
    R_mean <- R_instantaneous$R$`Mean(R)`
    R_highHPD <- R_instantaneous$R$`Quantile.0.975(R)`
    R_lowHPD <- R_instantaneous$R$`Quantile.0.025(R)`
  }
  
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
  result$estimate_type <- paste0(method, "_", variationType)
  
  return(result)
}


doReEstimation <- function(data_subset, region_i, data_type_i,  replicateNum, slidingWindow=1, methods, variationTypes, interval_ends=c("2020-04-01"), delays, truncations) {
  
  end_result <-  data.frame(date=c(), region=c(), value=c(),data_type=c(), variable=c(), estimate_type=c(), replicate=c())
  
  for(method_i in methods) {
    
    for(variation_i in variationTypes) {
      
      incidence_data <- data_subset$value[data_subset$variable == "incidence"]
      dates <- data_subset$date[data_subset$variable == "incidence"]
      
      offsetting <- delays[method_i]
      
      leftTrunc <- truncations$left[method_i]
      rightTrunc <- truncations$right[method_i]
      
      result <- estimateRe(dates=dates, 
                           incidenceData=incidence_data, 
                           windowLength =  slidingWindow,
                           estimateOffsetting = offsetting, 
                           rightTruncation = rightTrunc, 
                           leftTruncation=leftTrunc, 
                           method=method_i,
                           variationType = variation_i,
                           interval_ends = interval_ends)
      
      if(nrow(result) > 0) {
        
        result$region <- region_i
        result$data_type <- data_type_i
        result$replicate <- replicateNum
        ## need to reorder columns in 'results' dataframe to do the same as in data
        result <- result[,c(1,5,3,6,2,4,7)]
        
        end_result <- rbind(end_result ,result)
        
      }
    }
  }
  
  return(end_result)
}

## Perform R(t) estimations with EpiEstim on each 'region' of the data, with each 'method' and on each 'data_type'
## 'region' is the geographical region
## 'data_type' can be 'confirmed' for confirmed cases, 'deaths' for fatalities, 'hospitalized' for hospitalization data directly from hospitals (not via openZH here)
doAllReEstimations <- function(data, slidingWindow=3 ,methods=c("Cori", "WallingaTeunis"), variationTypes=c("step", "slidingWindow"), all_delays, truncations, interval_ends=c("2020-04-01")) {
  
  results_list <- list(data)
  
  for(region_i in unique(data$region)) {
    
    print(region_i)
    subset_data_region <- subset(data, region == region_i)
    
    for(data_type_i in unique(subset_data_region$data_type)) {
      
      print(data_type_i)
      subset_data <- subset(subset_data_region, data_type == data_type_i)
      
      delay_i <- all_delays[[data_type_i]]
      
      if(is.na(unique(subset_data$replicate))) {
        
        results_list <- c(results_list, list(doReEstimation(subset_data, region_i, data_type_i, replicateNum=0,
                                                            variationTypes=variationTypes,
                                                            interval_ends=interval_ends,
                                                            slidingWindow=slidingWindow, 
                                                            delays=delay_i, 
                                                            truncations=truncations, 
                                                            methods=methods)))
        
  
        
      } else {
        
        for (replicate_i in unique(unique(subset_data$replicate))) {
          subset_data_rep <- subset(subset_data, subset_data$replicate == replicate_i)
          
          results_list <- c(results_list, list(doReEstimation(subset_data_rep, 
                                                              region_i, 
                                                              data_type_i, 
                                                              replicateNum=replicate_i, 
                                                              slidingWindow=slidingWindow, 
                                                              methods=methods,
                                                              variationTypes=variationTypes,
                                                              interval_ends=interval_ends,
                                                              delays=delay_i, 
                                                              truncations=truncations)))
        }
        
      }
    }
  }
  return(rbind.fill(results_list))
  # return(rbind(data, fullResults))
}


### Make plot and csv files for "https://bsse.ethz.ch/cevo/research/sars-cov-2/real-time-monitoring-in-switzerland.html"
makeWebsitePlotAndFiles <- function(meltData, cantonList, lastDayBAGData,   startDate=as.Date("2020-03-07"), endDate=(Sys.Date() - 11)){
  
  meltData$replicate <- as.factor(meltData$replicate)
  
  #### Plot
  castData <- cast(meltData)
  castData$estimated <- !is.na(castData$estimate_type)
  castData$region <- factor(castData$region, levels=cantonList)

  estimates <- subset(castData, estimated==T & estimate_type %in% c("Cori_step", "Cori_slidingWindow") & data_type %in% c("infection_confirmed", "infection_deaths", "infection_hospitalized"))
  estimates <- subset(estimates, !(data_type == "infection_deaths" & date > (Sys.Date() - 16) ) & !(data_type == "infection_hospitalized" & date > lastDayBAGData))
  
  estimates$data_type <- factor(estimates$data_type, levels=c("infection_deaths", "infection_hospitalized","infection_confirmed"))
  
  ## Compute median and uncertainty intevals, grouping by everything but replicates
  estimates$median_R_mean <- with(estimates, ave(R_mean, date, region, data_type, estimate_type, FUN = median ))
  estimates$median_R_highHPD <- with(estimates, ave(R_highHPD, date, region, data_type, estimate_type, FUN = median ))
  estimates$median_R_lowHPD <- with(estimates, ave(R_lowHPD, date, region, data_type, estimate_type, FUN = median ))
  
  estimates$highQuantile_R_highHPD <- with(estimates, ave(R_highHPD, date, region, data_type, estimate_type, FUN = function(x) quantile(x, probs=0.975, na.rm=T) ))
  estimates$lowQuantile_R_lowHPD <- with(estimates, ave(R_lowHPD, date, region, data_type, estimate_type, FUN = function(x) quantile(x, probs=0.025, na.rm=T) ))
  
  dataCases <- subset(castData, estimated==F  & data_type %in% c("confirmed", "deaths", "hospitalized"))
  
  ## Incidence panel
  pCases <- ggplot(dataCases, aes(x=date)) +
    facet_grid(region ~.) +
    geom_line(aes(y = cumul, group=data_type, color=data_type), size=1) + 
    geom_bar(aes(y = incidence, fill=data_type), stat = "identity", position=position_dodge(preserve="single"), width=1,alpha=1) + 
    scale_x_date(date_breaks = "6 days", 
                 date_labels = '%b\n%d',
                 limits = c(as.Date("2020-02-25"), Sys.Date())) +
    scale_y_log10() + 
    ylab("Cumulative (line) and daily (bars) numbers") + 
    xlab("") +
    scale_colour_manual(values=c("black", gg_color(3)[c(1,3)]),
                        labels=c("Confirmed cases", "Hospitalizations", "Deaths"),
                        breaks=c("confirmed", "hospitalized", "deaths"),
                        name  ="Data source", 
                        aesthetics = c("colour", "fill")) +
    theme_bw() + 
    theme(
      strip.background = element_blank(),
      strip.text.y = element_blank(),
      axis.text.y= element_text(size=14),
      axis.text.x= element_text(size=14),
      axis.title.y =  element_text(size=17),
      legend.title = element_text(size=17),
      legend.text = element_text(size=15)
    )
  
  ## panel for Re estimates with sliding window
  pRe_window <- ggplot(subset(estimates, estimate_type=="Cori_slidingWindow"), aes(x=date)) +
    facet_grid(region ~.) +
    geom_ribbon(aes(ymin=median_R_lowHPD,ymax=median_R_highHPD, fill=data_type),alpha=0.7, colour=NA) +
    geom_ribbon(aes(ymin=lowQuantile_R_lowHPD,ymax=highQuantile_R_highHPD, fill=data_type),alpha=0.15, colour=NA) +
    geom_line(aes(y = median_R_mean, group=data_type, color=data_type), size=1.1) +
    geom_hline(yintercept = 1, linetype="dashed") + 
    scale_x_date(date_breaks = "4 days", 
                 date_labels = '%b\n%d',
                 limits = c(startDate, endDate)) + 
    coord_cartesian(ylim=c(0,3)) +
    geom_vline(xintercept = c(as.Date("2020-03-14"), as.Date("2020-03-17"), as.Date("2020-03-20")), linetype="dotted") + 
    annotate("rect", xmin=as.Date("2020-03-14"), xmax=as.Date("2020-03-17"), ymin=-1, ymax=Inf, alpha=0.45, fill="grey") +
    scale_colour_manual(values=c(gg_color(3)[c(1,3)], "black"),
                        labels=c("Confirmed cases",  "Deaths", "Hospitalized"),
                        breaks=c("infection_confirmed", "infection_deaths", "infection_hospitalized"),
                        name  ="Data source",
                        aesthetics = c("fill", "color")) +
    xlab("") + 
    ylab("Reproductive number") + 
    theme_bw() + 
    theme(
      strip.background = element_blank(),
      strip.text.y = element_text(size=16),
      axis.text.y= element_text(size=14),
      axis.text.x= element_text(size=14),
      axis.title.y =  element_text(size=17),
      legend.title = element_text(size=14),
      legend.text = element_text(size=12)
    )
  
  ## panel with piecewise constant Re estimates
  pRe_step <- ggplot(subset(estimates, estimate_type=="Cori_step"), aes(x=date)) +
    facet_grid(region ~.) +
    geom_ribbon(aes(ymin=median_R_lowHPD,ymax=median_R_highHPD, fill=data_type),alpha=0.7, colour=NA) +
    geom_ribbon(aes(ymin=lowQuantile_R_lowHPD,ymax=highQuantile_R_highHPD, fill=data_type),alpha=0.15, colour=NA) +
    geom_line(aes(y = median_R_mean, group=data_type, color=data_type), size=1.1) +
    geom_hline(yintercept = 1, linetype="dashed") + 
    scale_x_date(date_breaks = "4 days", 
                 date_labels = '%b\n%d',
                 limits = c(startDate, endDate)) + 
    coord_cartesian(ylim=c(0,3)) +
    geom_vline(xintercept = c(as.Date("2020-03-14"), as.Date("2020-03-17"), as.Date("2020-03-20")), linetype="dotted") + 
    annotate("rect", xmin=as.Date("2020-03-14"), xmax=as.Date("2020-03-17"), ymin=-1, ymax=Inf, alpha=0.45, fill="grey") +
    scale_colour_manual(values=c(gg_color(3)[c(1,3)], "black"),
                        labels=c("Confirmed cases",  "Deaths", "Hospitalized"),
                        breaks=c("infection_confirmed", "infection_deaths", "infection_hospitalized"),
                        name  ="Data source",
                        aesthetics = c("fill", "color")) +
    xlab("") + 
    ylab("Reproductive number") + 
    theme_bw() + 
    theme(
      strip.background = element_blank(),
      strip.text.y = element_text(size=16),
      axis.text.y= element_text(size=14),
      axis.text.x= element_text(size=14),
      axis.title.y =  element_text(size=17),
      legend.title = element_text(size=14),
      legend.text = element_text(size=12)
    )
  
  ## make full plot
  ggarrange(pCases,pRe_window,pRe_step,
            nrow = 1, 
            labels = c("A", "B", "C"),
            font.label = list(size = 18),
            common.legend = TRUE,
            legend = "bottom")
  
  plotPath <- paste0("../Plots/Re_CH_", gsub("-","", Sys.Date()), ".png")
  ggsave(plotPath, width = 40, height = 60, units = "cm")
  plotPathCommon <- paste0("../Webpage_material/Re_CH.png")
  ggsave(plotPathCommon, width = 40, height = 60, units = "cm")
  
  
  #### Save estimates in CSV files
  regionsToSave <- cantonList
  
  dirPath_step <- file.path("../Estimates", paste0(Sys.Date(), "_step"))
  dirPath_window <- file.path("../Estimates", paste0(Sys.Date(), "_slidingWindow"))
  dir.create(dirPath_step, showWarnings = FALSE)
  dir.create(dirPath_window, showWarnings = FALSE)
  
  for (reg in regionsToSave) {
    
    estimates_confirmed <- subset(castData, estimated==T & estimate_type %in% c("Cori_slidingWindow", "Cori_step") & data_type %in% c("infection_confirmed") & date >= startDate & date <= endDate & region==reg)
    estimates_confirmed$median_R_mean <- with(estimates_confirmed, ave(R_mean, date, region, data_type, estimate_type, FUN = median ))
    estimates_confirmed$median_R_highHPD <- with(estimates_confirmed, ave(R_highHPD, date, region, data_type, estimate_type, FUN = median ))
    estimates_confirmed$median_R_lowHPD <- with(estimates_confirmed, ave(R_lowHPD, date, region, data_type, estimate_type, FUN = median ))
    
    estimates_confirmed <- subset(estimates_confirmed, replicate == 1)
    estimates_step <- subset(estimates_confirmed, estimate_type=="Cori_step")
    estimates_window <- subset(estimates_confirmed, estimate_type=="Cori_slidingWindow")
    
    drop_cols <- c("estimate_type", "data_type", "region", "replicate", "cumul", "incidence", "R_highHPD", "R_lowHPD", "R_mean", "estimated")
    
    data_to_save_step <- estimates_step[, !names(estimates_step) %in% drop_cols]
    data_to_save_window <- estimates_window[, !names(estimates_window) %in% drop_cols]
    
    colnames(data_to_save_step) <- c("date", "R_mean", "R_highCI", "R_lowCI")
    colnames(data_to_save_window) <- c("date", "R_mean", "R_highCI", "R_lowCI")
    
    write_excel_csv(format(data_to_save_step, digits=3), path = file.path(dirPath_step, paste0(reg, "_R_estimates.csv")), quote=F)
    write_excel_csv(format(data_to_save_window, digits=3), path = file.path(dirPath_window, paste0(reg, "_R_estimates.csv")), quote=F)
  }
  
  ## Create zip archive from each estimate type (to be uploaded to webpage)
  csvFiles <- dir(dirPath_step, full.names = TRUE)
  zipFile_step <- file.path("../Webpage_material", "Re_CH_step.zip")
  zip(zipfile = zipFile_step, flags="-r9Xj", files = csvFiles) # flag "-j" added  to default flags to not save entire dir tree
  
  csvFiles <- dir(dirPath_window, full.names = TRUE)
  zipFile_window <- file.path("../Webpage_material", "Re_CH_slidingWindow.zip")
  zip(zipfile = zipFile_window, flags="-r9Xj", files = csvFiles) # flag "-j" added to default flags to not save entire dir tree
  
}


#################################
#### Start of the script ########
#################################


####################
###### Input #######
####################

workDir <- "/Users/scirej/Documents/nCov19/Incidence_analysis/Scripts"

### Waiting time distributions ###
# incubation: mean = 5.3, sd =3.2 (Linton et al., best gamma distr fit)
meanIncubation <- 5.3
sdIncubation <- 3.2

# onset to test: data from BL canton
meanOnsetToTest <- 5.6
sdOnsetToTest <- 4.2

# onset to hospitalization report: pooled CH data from BAG (17/04/20 update)
meanOnsetToHosp <- 6.6
sdOnsetToHosp <- 5.1

# onset to death: mean =15.0 sd=6.9 (Linton et al. best gamma distr fit)
meanOnsetToDeath <- 15.0
sdOnsetToDeath <- 6.9

meanOnsetToCount <- c("confirmed"= meanOnsetToTest, "deaths"=meanOnsetToDeath, "hospitalized"=meanOnsetToHosp)
sdOnsetToCount <- c("confirmed"= sdOnsetToTest, "deaths"=sdOnsetToDeath, "hospitalized"=sdOnsetToHosp)

### Date input
interval_ends <- c("2020-03-13", "2020-03-16", "2020-03-20")
window <- 3
lastDayBAGData <- as.Date("2020-04-23")

### Delays applied
all_delays <- list(infection_confirmed=c(Cori=0, WallingaTeunis=-5),
                   infection_deaths=c(Cori=0, WallingaTeunis=-5),
                   infection_hospitalized=c(Cori=0, WallingaTeunis=-5),
                   confirmed=c(Cori=10, WallingaTeunis=5),
                   deaths=c(Cori=20, WallingaTeunis=15),
                   hospitalized=c(Cori=8, WallingaTeunis=3))

truncations <- list(left=c(Cori=5, WallingaTeunis=0),
                    right=c(Cori=0, WallingaTeunis=8))


replicates <- 100
orderedListOfRegions <- c("AG", "BE", "BL", "BS", "FR", "GE", "GR", "LU", "NE", "SG", "TI", "VD", "VS", "ZH", "CH")


###############
setwd(workDir)

### Get data
raw_data <- getAllSwissData(stoppingAfter = (Sys.Date()-1))

swissData <- subset(raw_data, region %in% orderedListOfRegions & !(region != "CH" & data_type %in% c("deaths")))
## need to fix script to allow for not subsetting like this (pb with some canton death timeseries)

### Sample infection dates
drawnInfectTimesData <- drawAllInfectionDates(swissData, source_data=c("confirmed", "deaths", "hospitalized"), 
                                              numberOfReplicates = replicates, 
                                              meanIncubation = meanIncubation, sdIncubation = sdIncubation,
                                              meanOnsetToCount=meanOnsetToCount, sdOnsetToCount=sdOnsetToCount)

### Run EpiEstim
data <- doAllReEstimations(drawnInfectTimesData, slidingWindow=window, 
                           methods="Cori",
                           all_delays=all_delays, 
                           truncations=truncations,
                           interval_ends = interval_ends)


makeWebsitePlotAndFiles(data, orderedListOfRegions, lastDayBAGData = lastDayBAGData)