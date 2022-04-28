#install.packages("tidyverse")
#install.packages("ggpubr")

library(tidyverse)
library(ggplot2)
library(dplyr)
library(tidyr)
#library(ggpubr)


#require(gridExtra)

##
##
## Spec => []Inv /\\ ATDSpec
data <- read.csv(header=TRUE, sep = "#", file = 
                   "/Users/markus/src/TLA/_specs/ewd998/SmokeEWD998_SC1651106251.csv")

summary <- data %>%
  group_by(BugFlags) %>%
  summarize(
    "ATDSpec" = length(BugFlags[Violation==13]),
    "Inv" = length(BugFlags[Violation==12]),
    "None" = length(BugFlags[Violation==0])
    ,V = length(BugFlags[Violation!=0])
  )

## https://mgimond.github.io/ES218/Week03b.html
df <- pivot_longer(summary, cols=2:4, names_to = "Violation", values_to = "Percentage")

#p1 <- 
  ggplot(df, aes(fill=Violation, y=Percentage, x=BugFlags)) + 
  geom_bar(position="fill", stat="identity") +
  ggtitle("Violations found with random simulation checking\nSpec => []Inv /\\ ATDSpec.") +
  xlab("Bugs present")

##
##
## TypeOK /\ Inv!P0 /\ [Next]_vars => []Inv
data <- read.csv(header=TRUE, sep = "#", file = "/Users/markus/src/TLA/_specs/ewd998/SmokeEWD998_SC1651092004.csv")

summary <- data %>%
  group_by(BugFlags) %>%
  summarize(
    "None" = length(BugFlags[Violation==0]),
    "ATDSpec" = length(BugFlags[Violation==13]),
    "Inv" = length(BugFlags[Violation==12])
    ,V = length(BugFlags[Violation!=0])
  )

## https://mgimond.github.io/ES218/Week03b.html
df <- pivot_longer(summary, cols=2:4, names_to = "Violation", values_to = "Percentage")

#p2 <- 
  ggplot(df, aes(fill=Violation, y=Percentage, x=BugFlags)) + 
  geom_bar(position="fill", stat="identity") +
  ggtitle("Violations found with random simulation checking\nTypeOK /\\ Inv!P0 /\\ [Next]_vars => []Inv\nstarting from a small, randomly choosen subset\nof the initial states.") +
  xlab("Bugs present")



##
##
## TypeOK /\ Inv!P0 /\ [Next]_vars => []Inv /\ ATDSpec
data <- read.csv(header=TRUE, sep = "#", file = "/Users/markus/src/TLA/_specs/ewd998/SmokeEWD998_SC1651080428.csv")

summary <- data %>%
  group_by(BugFlags) %>%
  summarize(
    "None" = length(BugFlags[Violation==0]),
    "ATDSpec" = length(BugFlags[Violation==13]),
    "Inv" = length(BugFlags[Violation==12])
    #    ,V = length(BugFlags[Violation!=0])
  )

## https://mgimond.github.io/ES218/Week03b.html
df <- pivot_longer(summary, cols=2:4, names_to = "Violation", values_to = "Percentage")

p3 <- ggplot(df, aes(fill=Violation, y=Percentage, x=BugFlags)) + 
  geom_bar(position="fill", stat="identity") +
  ggtitle("Violations found with random simulation checking\nTypeOK /\\ Inv!P0 /\\ [Next]_vars => []Inv /\\ ATDSpec\nstarting from a small, randomly choosen subset\nof the initial states.") +
  xlab("Bugs present")



grid.arrange(p1, p2, p3, ncol=1)










#res <- data %>% group_by(data$BugFlags) # %>% count(data$Violations)
#res["L"] <- res
#plot(frob)



######

## https://r-graph-gallery.com/48-grouped-barplot-with-ggplot2.html

# create a dataset
specie <- c(rep("sorgho" , 3) , rep("poacee" , 3) , rep("banana" , 3) , rep("triticum" , 3) )
condition <- rep(c("normal" , "stress" , "Nitrogen") , 4)
value <- abs(rnorm(12 , 0 , 15))
data <- data.frame(specie,condition,value)

# Stacked + percent
ggplot(data, aes(fill=condition, y=value, x=specie)) + 
  geom_bar(position="fill", stat="identity")