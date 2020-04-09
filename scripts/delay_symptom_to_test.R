rm(list=ls())

library("ggplot2")
library("lubridate")
library("readr")
library("EpiEstim")
library("gridExtra")
library("reshape2")


##### Quick script to plot histogram of delay between symptom onset and testing in BS hospital data

dataSymptoms <- read.csv(sep=";", stringsAsFactors = F,na.strings = c("","NA"),
                         "../data/Delay_test_symptoms.csv")

rawDataSymptoms <- dataSymptoms[,-c(1,3)]

rawDataSymptoms <- rawDataSymptoms[complete.cases(rawDataSymptoms),]

startSymptoms <- dmy(rawDataSymptoms$Manifestationsbeginn)
testDate<- dmy(rawDataSymptoms$Eingangsdatum_LM)

datesSymptoms <- data.frame(startSymptoms=startSymptoms, testDate=testDate )
datesSymptoms$timeFromSymptomsToTest <- datesSymptoms$testDate - datesSymptoms$startSymptoms

ggplot(datesSymptoms, aes(x=timeFromSymptomsToTest)) +
  geom_histogram(color="black", fill="grey", binwidth = 1) +
  theme_bw() +
  ylab("Count") +
  xlab("Days") +
  theme(
    axis.text.y= element_text(size=17),
    axis.text.x= element_text(size=17),
    axis.title.x =  element_text(size=19),
    axis.title.y =  element_text(size=19)
  )

plotPath <- "../plots/Fig1_Histogram_delay_symptoms_to_test_report.png"
ggsave(plotPath, width = 15, height = 15, units = "cm")

mean(as.numeric(datesSymptoms$timeFromSymptomsToTest)) #5.3 on 91 datapoints
sd(as.numeric(datesSymptoms$timeFromSymptomsToTest)) # 3.8