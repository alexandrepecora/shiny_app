
library(shiny)
library(rsconnect)
library(magrittr)
library(lubridate)
library(stringr)
library(tibble)
library(broom)
library(ggplot2)
library(gt)
library(knitr)
library(devtools)
library(foreach)
library(dplyr)
library(data.table)
library(httr)
library(scales)
library(tidyr)

options(scipen=999)

## Define the simulate function
simulate <- function(
    quar.rate = 0, ## Rate at which an individual goes from Susceptible to Quarantined
    max_quar = 0, # Quarantine peak 
    quar.rate.i = 1, ## Rate at which an individual goes from Infected to Quarantined Infected
    ## Transmission paratemters 
    lambda = 14, ## Encounters between Susceptible and Infected (symptomatic) per day
    rho_s = 0.012, ## Infection probability between Susceptible and Infected (symptomatic) => AKA rate of transmission
    rho_a = 0.012, ## Infection probability between Susceptible and Exposed
    lambda_q = 7, ## Quarantine encounters (lambda_q / lambda = efficiency in reducing contacts) 
    ## Medical parameters
    prog.rate = 1/5.2,     # Rate per day from Exposed to Infected (symptomatic)
    rec.rate = 1/14,      # Rate per day from Infected (symptomatic) to Recovered 
    hosp.rate = 1/100,    # Rate per day from Infected to Hospitalization
    disch.rate = 1/7,     # Rate per day from Hospitalization to Recovered 
    fat.rate.base = 1/50, # Rate per day from Hospitalization to Fatality
    total_time,
    initial) {
    
    sim.matrix <- data.frame(matrix(NA, nrow = total_time, ncol = 10))
    colnames(sim.matrix) <- names(initial)
    
    sim.matrix$time[1] = initial[1]    
    sim.matrix$s.num[1] = initial[2]  
    sim.matrix$e.num[1] = initial[3]  
    sim.matrix$i.num[1] = initial[4]  
    sim.matrix$q.num[1] = initial[5]  
    sim.matrix$qe.num[1] = initial[6]  
    sim.matrix$qi.num[1] = initial[7]    
    sim.matrix$h.num[1] = initial[8]  
    sim.matrix$r.num[1] = initial[9]  
    sim.matrix$f.num[1] = initial[10]  
    
    for (t in 2:total_time) {
        
        sim.matrix$time[t] = t
        sim.matrix$s.num[t] <- max(sim.matrix$s.num[t-1],0) ## Initial S
        sim.matrix$e.num[t] <- sim.matrix$e.num[t-1]  ## Initial E
        sim.matrix$i.num[t] <- sim.matrix$i.num[t-1]  ## Initial I
        sim.matrix$q.num[t] <- sim.matrix$q.num[t-1]  ## Initial Q
        sim.matrix$qe.num[t] <- sim.matrix$qe.num[t-1]  ## Initial QE
        sim.matrix$qi.num[t] <- sim.matrix$qi.num[t-1]  ## Initial QI
        sim.matrix$h.num[t] <- sim.matrix$h.num[t-1]  ## Initial H
        sim.matrix$f.num[t] <- sim.matrix$f.num[t-1]  ## Initial F
        sim.matrix$r.num[t] <- sim.matrix$r.num[t-1]  ## Initial R
        
        # Mass of quarantined and non quarantined (M)
        M = lambda * (sim.matrix$s.num[t] + sim.matrix$e.num[t] + sim.matrix$i.num[t] + sim.matrix$r.num[t]) +
            lambda_q * (sim.matrix$q.num[t] + sim.matrix$qe.num[t] + sim.matrix$qi.num[t])
        # MASS of infected (symptomatic (I) + asymptomatic (E) )
        MI = ( lambda*(sim.matrix$i.num[t] + sim.matrix$e.num[t]) + 
                   lambda_q*(sim.matrix$qi.num[t] + sim.matrix$qe.num[t]) )
        
        # Identifying probability of Exposed or Infected 
        pi_I =  MI / M
        # Identifying probability of Infected (symptomatic), given Exposure 
        pi_II = (lambda*sim.matrix$i.num[t] + lambda_q*sim.matrix$qi.num[t])  /  MI
        # Identifying probability of Non Symptomatic (E), given Exposure 
        pi_IE = (lambda*sim.matrix$e.num[t] + lambda_q*sim.matrix$qe.num[t])  /  MI
        
        # Identifying probability of Infection, conditional on a random meeting: 
        alpha =  pi_I*(pi_II*rho_s + pi_IE*rho_a)
        
        # Verifying if quarantine reached the peak
        q_rate <- ifelse( 
            sim.matrix$q.num[t]/(sum(sim.matrix[t,2:10]) - sim.matrix$f.num[t] - sim.matrix$h.num[t]) < max_quar,
            quar.rate,
            0)
        
        ## FROM S to Q
        trans_S_Q <- q_rate * sim.matrix$s.num[t]
        sim.matrix$s.num[t] <- sim.matrix$s.num[t] - trans_S_Q ## Update S
        sim.matrix$q.num[t] <- sim.matrix$q.num[t] + trans_S_Q ## Update Q
        
        ## FROM S to E
        trans_S_E <-  (alpha * lambda) * sim.matrix$s.num[t]
        
        sim.matrix$s.num[t] <- sim.matrix$s.num[t] - trans_S_E ## Update S
        sim.matrix$e.num[t] <- sim.matrix$e.num[t] + trans_S_E ## Update E
        
        ## FROM E to I
        trans_E_I <-  sim.matrix$e.num[t]*prog.rate
        
        sim.matrix$e.num[t] <- sim.matrix$e.num[t] - trans_E_I ## Update E
        sim.matrix$i.num[t] <- sim.matrix$i.num[t] + trans_E_I ## Update I
        
        ## FROM (Q, E) to QE
        trans_Q_QE <-  (alpha * lambda_q) * sim.matrix$q.num[t]
        trans_E_QE <- sim.matrix$e.num[t] * q_rate
        
        sim.matrix$q.num[t] <- sim.matrix$q.num[t] - trans_Q_QE ## Update Q
        sim.matrix$e.num[t] <- sim.matrix$e.num[t] - trans_E_QE ## Update E
        sim.matrix$qe.num[t] <- sim.matrix$qe.num[t] + trans_Q_QE + trans_E_QE ## Update QE
        
        ## FROM (QE, I) to QI
        trans_QE_QI <-  sim.matrix$qe.num[t]*prog.rate
        trans_I_QI <-  sim.matrix$i.num[t]*quar.rate.i
        
        sim.matrix$qe.num[t] <- sim.matrix$qe.num[t] - trans_QE_QI ## Update QE
        sim.matrix$i.num[t] <- sim.matrix$i.num[t] - trans_I_QI ## Update I 
        sim.matrix$qi.num[t] <- sim.matrix$qi.num[t] + trans_QE_QI + trans_I_QI ## Update QI
        
        ## FROM (I, QI) to H
        trans_I_H <-  sim.matrix$i.num[t]*hosp.rate
        trans_QI_H <-  sim.matrix$qi.num[t]*hosp.rate
        
        sim.matrix$i.num[t] <- sim.matrix$i.num[t] - trans_I_H ## Update I
        sim.matrix$qi.num[t] <- sim.matrix$qi.num[t] - trans_QI_H ## Update QI
        sim.matrix$h.num[t] <- sim.matrix$h.num[t] + trans_I_H + trans_QI_H ## Update H
        
        ## FROM (I, QI, H) to R
        trans_I_R <-  sim.matrix$i.num[t]*rec.rate
        trans_QI_R <-  sim.matrix$qi.num[t]*rec.rate
        trans_H_R <-  sim.matrix$h.num[t]*disch.rate
        
        sim.matrix$i.num[t] <- sim.matrix$i.num[t] - trans_I_R ## Update I
        sim.matrix$qi.num[t] <- sim.matrix$qi.num[t] - trans_QI_R ## Update QI
        sim.matrix$h.num[t] <- sim.matrix$h.num[t] - trans_H_R ## Update H
        sim.matrix$r.num[t] <- sim.matrix$r.num[t] + trans_I_R + trans_QI_R + trans_H_R ## Update R
        
        ## FROM H to F
        trans_H_F <-  sim.matrix$h.num[t]*fat.rate.base
        
        sim.matrix$h.num[t] <- sim.matrix$h.num[t] - trans_H_F ## Update H
        sim.matrix$f.num[t] <- sim.matrix$f.num[t] + trans_H_F ## Update F
        
    }
    
    ## Adding up total infections
    sim.matrix$ti.num = (sim.matrix$i.num + sim.matrix$qi.num) 
    
    return(sim.matrix)
}


plot1 <- function(sim_data, x_limit) {
    ## Visualizing prevalence:
    baseline_plot <- sim_data %>% # use only the prevalence columns
        select(time, ti.num, h.num, f.num) %>% 
        filter(time <= x_limit) %>% 
        pivot_longer(-c(time), names_to = "Groups", 
                     values_to = "count")
    
    ## Define a standard set of colours to represent compartments and plot 
    compcols <- c(ti.num = "orange", 
                  h.num = "red", 
                  f.num = "black")
    complabels <- c(ti.num = "Infected/infectious",  
                    h.num = "Requires hospitalisation", 
                    f.num = "Case fatality")
    baseline_plot %>% ggplot(aes(x = time, y = count, colour = Groups)) + 
        geom_line(size = 2, alpha = 0.7) + 
        scale_colour_manual(values = compcols, 
                            labels = complabels) +
        scale_y_continuous(label = comma) +
        labs(title = "Simulation Results", 
             x = "Days since beginning of epidemic", y = "Prevalence (persons)") +
        theme(legend.position="bottom")
}

plot2 <- function(sim_data, x_limit, icu_beds) {
    ## Visualizing prevalence:
    sim_data$icu <- icu_beds
    
    baseline_plot <- sim_data %>% # use only the prevalence columns
        select(time, h.num, f.num, icu) %>% 
        filter(time <= x_limit) %>% 
        pivot_longer(-c(time), names_to = "Groups", 
                     values_to = "count")
    
    ## Define a standard set of colours to represent compartments and plot 
    compcols <- c(h.num = "red", 
                  f.num = "black", 
                  icu = "cyan")
    complabels <- c(h.num = "Requires hospitalisation", 
                    f.num = "Case fatality",
                    icu = "Number of ICU beds")
    baseline_plot %>% ggplot(aes(x = time, y = count, colour = Groups)) + 
        geom_line(size = 2, alpha = 0.7) + 
        scale_colour_manual(values = compcols, 
                            labels = complabels) +
        scale_y_continuous(label = comma) +
        labs(title = "Simulation Results", 
             x = "Days since beginning of epidemic", y = "Prevalence (persons)")  +
        theme(legend.position="bottom")
}

plot_backtest <- function(sim_data1, sim_data2, x_lim) {
    
    sim <- sim_data1
    
    sim_quar <- sim_data2
    
    load_data_sp <- function(case_initial) {
        raw <- fread("https://raw.githubusercontent.com/seade-R/dados-covid-sp/master/data/dados_covid_sp.csv")
        
        dt <- raw[, c("datahora", "casos", "obitos") ]
        dt <- dt[,lapply(.SD,sum),by="datahora"] 
        dt <- dt[casos > case_initial]
        
        dt <- dt[,-c("datahora", "casos")]
        dt <- dt[, time := sequence(.N)]
        setcolorder(dt, c("time", "obitos"))
        setnames(dt, "obitos", "f.num")
        
        return(dt)
    }
    
    dt_sp <- load_data_sp(case_initial = 1)
    dt_sp <- dt_sp[,"region" := "SP"]
    
    day_limit <- x_lim ## set limit day when pulling data from model
    
    model <- sim %>% select(time, f.num) %>% filter(time <= day_limit)
    model <- setDT(model)
    model <- model[, "region" := "model"]
    
    model_quar <- sim_quar %>% select(time, f.num) %>% filter(time <= day_limit)
    model_quar <- setDT(model_quar)
    model_quar <- model_quar[, "region" := "model_quar"]
    
    dt_backtest <- rbind(dt_sp, model, model_quar, fill = T)
    
    ## PLOT: PREDICTED VS REALIZED: SP 
    group.colors <- c(SP = "green", model = "black", model_quar = "blue")
    complabels <- c(model = "Sem quarentena", model_quar = "Com quarentena")
    y_lim <- max(dt_backtest[ time < day_limit, f.num])
    # Plot
    ggplot(data = dt_backtest, aes(x = time, y = f.num)) +
        geom_line(aes(color = factor(region))) + geom_point(shape=1, alpha = 0.5) +
        xlim(1, day_limit) + ylim(NA,y_lim) +  scale_color_manual(values=group.colors, labels = complabels) + 
        scale_y_continuous(label = comma, limits=c(0, y_lim)) +
        theme(legend.title=element_blank())  +
        labs(title = "Projetado x Realizado", 
             x = "Days since beginning of epidemic", y = "Prevalence (persons)") + theme(legend.title=element_blank())
    
}

economy <- function(pop, x_limit, sim_data1, sim_data2) {
    
    population <- pop 
    
    economy_base <- sim_data1 %>% # use only the prevalence columns
        select(time, i.num, h.num, f.num, q.num, qi.num) %>% 
        # examine only the first 100 days since it is all over by
        # then using the default parameters
        filter(time <= x_limit)
    
    economy_base$qi.perc <- economy_base$qi.num/population
    economy_base$h.perc <- economy_base$h.num/population
    economy_base$f.perc <- economy_base$f.num/population
    economy_base$q.perc <- economy_base$q.num/population
    economy_base$gdp <- 1 - economy_base$qi.perc - economy_base$h.perc - economy_base$f.perc - economy_base$q.perc*0.5  
    
    ## Storing the number of infected and fatalities in the next year
    economy_sim <- sim_data2 %>% # use only the prevalence columns
        select(time, i.num, h.num, f.num, q.num, qi.num) %>% 
        # examine only the first 100 days since it is all over by
        # then using the default parameters
        filter(time <= x_limit)
    
    economy_sim$qi.perc <- economy_sim$qi.num/population
    economy_sim$h.perc <- economy_sim$h.num/population
    economy_sim$f.perc <- economy_sim$f.num/population
    economy_sim$q.perc <- economy_sim$q.num/population
    economy_sim$gdp <- 1 - economy_sim$qi.perc - economy_sim$h.perc - economy_sim$f.perc - economy_sim$q.perc*0.5  
    
    economy <- data.frame(economy_base$gdp)
    
    economy <- economy_base %>% select(time, gdp)
    economy <- cbind(economy, economy_sim$gdp )
    names(economy)[2] <- "gdp_base"
    names(economy)[3] <- "gdp_sim"
    
    ## Visualizing gdp effect:
    economy_plot_df <- economy %>% # use only the prevalence columns
        select(time, gdp_base, gdp_sim) %>% 
        # examine only the first 100 days since it is all over by
        # then using the default parameters
        filter(time <= 360) %>% pivot_longer(-c(time), names_to = "Groups", 
                                             values_to = "count")
    # define a standard set of colours to represent compartments
    compcols <- c(gdp_base = "black", gdp_sim = "blue" )
    complabels <- c(gdp_base = "Baseline", gdp_sim = "Quarantine")
    economy_plot_df %>% ggplot(aes(x = time, y = count, colour = Groups)) + 
        geom_line(size = 2, alpha = 0.7) + 
        scale_colour_manual(values = compcols, 
                            labels = complabels) + 
        labs(title = "GDP Impact: Simulation vs Non-Quarantine", 
             x = "Days since beginning of epidemic", y = "GDP") +
        theme(legend.position="bottom")
}


# Define UI for app that simulates and draws the curves ----
ui <- shinyUI(fluidPage(
    
    # App title ----
    titlePanel("Simulador: SEIR + Quarentena + Economia"),
    
    plotOutput(outputId = "plot1"),
    plotOutput(outputId = "plot2"),
    plotOutput(outputId = "plot3"),
    fluidRow(column(4, numericInput(inputId = "input_xaxis1",
                                    label = "Input max days in X axis",
                                    min = 1,
                                    max = 720,
                                    value = 360))),
    
    # Sidebar panel for inputs ----
    fluidRow(
        
        actionButton("go", "Calculate"),
        actionButton("reset", "Reset parameters"),
        
        column(4, 
               
               h4(textOutput(outputId = "caption1")),
               
               sliderInput(inputId = "input_lambda",
                           label = "Daily encounters:",
                           min = 1,
                           max = 50,
                           value = 14),
               
               sliderInput(inputId = "input_rho",
                           label = "Infection probability (%):",
                           min = 0.5,
                           max = 5,
                           step = 0.1,
                           value = 1.2, 
                           round = T),
               
               sliderInput(inputId = "input_prog",
                           label = "Number of days: Exposed to Infected",
                           min = 1,
                           max = 20,
                           step = 0.1,
                           value = 5.2, 
                           round = T),
               
               sliderInput(inputId = "input_rec",
                           label = "Number of days: Infected to Recovered",
                           min = 1,
                           max = 20,
                           step = 0.1,
                           value = 14, 
                           round = T),
               
               sliderInput(inputId = "input_hosp",
                           label = "Probability of hospitalization, given Infection (%)",
                           min = 0.1,
                           max = 10,
                           step = 0.1,
                           value = 1, 
                           round = T),
               
               sliderInput(inputId = "input_hosprec",
                           label = "Number of days: Hospitalization to Recovered",
                           min = 1,
                           max = 25,
                           step = 1,
                           value = 7, 
                           round = T),
               
               sliderInput(inputId = "input_fat",
                           label = "Probability of Fatality, given Hospitalization (%)",
                           min = 0.1,
                           max = 20,
                           step = 0.1,
                           value = 2, 
                           round = T)
               
        ),
        
        column(4,
               
               h4(textOutput(outputId = "caption2")),
               
               sliderInput(inputId = "input_lambda_q",
                           label = "Daily encounters (in quarantine):",
                           min = 1,
                           max = 50,
                           value = 7),
               
               sliderInput(inputId = "input_quar",
                           label = "Daily quarantine rate (%)",
                           min = 0,
                           max = 10,
                           step = .5,
                           value = 3, 
                           round = T),
               
               sliderInput(inputId = "input_maxquar",
                           label = "Maximum quarantined population (%)",
                           min = 0,
                           max = 100,
                           step = 1,
                           value = 50, 
                           round = T)          
        ),
        
        column(4,
               
               h4(textOutput(outputId = "caption3")),
               
               numericInput(inputId = "input_pop",
                            label = "Population",
                            value = 44000000),
               
               numericInput(inputId = "input_popinf",
                            label = "Initial population infected",
                            value = 5000),
               
               numericInput(inputId = "input_popinfa",
                            label = "Initial population infected (asymptomatic)",
                            value = 10000),
               
               numericInput(inputId = "input_icu",
                            label = "Number of ICU beds",
                            value = 100000)
        )
    ),
    plotOutput(outputId = "plot4"),
    
    fluidRow(column(4, numericInput(inputId = "input_xaxis",
                                    label = "Input max days in X axis",
                                    min = 1,
                                    max = 720,
                                    value = 100)))
    
))


server <- function(input, output, session) {
    
    # 0. Reset sliders to initial values after clicking RESET
    observeEvent(input$reset,{
        updateSliderInput(session,'input_lambda',value = 14)
        updateSliderInput(session,'input_rho',value = 1.2)
        updateSliderInput(session,'input_prog',value = 5.2)
        updateSliderInput(session,'input_rec',value = 14)
        updateSliderInput(session,'input_hosp',value = 1)
        updateSliderInput(session,'input_hosprec',value = 7)
        updateSliderInput(session,'input_fat',value = 2)
        updateSliderInput(session,'input_quar',value = 3)
        updateSliderInput(session,'input_maxquar',value = 50)
        updateSliderInput(session,'input_lambda_q',value = 7)
    })
    
    # 1. Update data after clicking buttom
    sim_data_quar <- eventReactive(input$go, {
        simulate(
            initial = c(
                time = 1,
                s.num = input$input_pop,
                e.num = input$input_popinf,
                i.num = input$input_popinf,
                q.num = 0,
                qe.num = 0,
                qi.num = 0,
                h.num = 0,
                r.num = 0,
                f.num = 0), 
            total_time = 720,
            ## Parameters
            lambda = input$input_lambda,
            rho_s = input$input_rho/100,
            rho_a = input$input_rho/100,
            prog.rate = 1/input$input_prog,
            rec.rate = 1/input$input_rec,
            hosp.rate = input$input_hosp/100,
            disch.rate = 1/input$input_hosprec,
            fat.rate.base = input$input_fat/100,
            quar.rate = input$input_quar/100,
            max_quar = input$input_maxquar/100,
            lambda_q = input$input_lambda_q
        )
        
    }, ignoreNULL = FALSE) 

    sim_data_noquar <- eventReactive(input$go, {
        simulate(initial = c(
            time = 1,
            s.num = input$input_pop,
            e.num = input$input_popinf,
            i.num = input$input_popinf,
            q.num = 0,
            qe.num = 0,
            qi.num = 0,
            h.num = 0,
            r.num = 0,
            f.num = 0),
            total_time = 720,
            ## Parameters
            lambda = input$input_lambda,
            rho_s = input$input_rho/100,
            rho_a = input$input_rho/100,
            prog.rate = 1/input$input_prog,
            rec.rate = 1/input$input_rec,
            hosp.rate = input$input_hosp/100,
            disch.rate = 1/input$input_hosprec,
            fat.rate.base = input$input_fat/100,
            quar.rate = 0,
            max_quar = input$input_maxquar/100,
            lambda_q = input$input_lambda_q)
    }, ignoreNULL = FALSE)    

    
    # 2. Its output type is a plot
    
    output$caption1 <- renderText({ "Medical Parameters" })
    
    output$caption2 <- renderText({ "Quarantine Parameters" })
    
    output$caption3 <- renderText({ "Population Parameters" })
    
    output$plot1 <- renderPlot({
        
        plot1(x_limit = input$input_xaxis1 , 
              sim_data = sim_data_quar())
        
    }) 
    
    output$plot2 <- renderPlot({
        
        plot2(x_limit = input$input_xaxis1,
              sim_data = sim_data_quar(), icu_beds = input$input_icu)
        
    }) 
    
    output$plot3 <- renderPlot({
        
        economy(x_limit = input$input_xaxis1, 
                pop = input$input_pop, 
                sim_data1 = sim_data_noquar(), 
                sim_data2 = sim_data_quar())
        
    }) 
    
    output$plot4 <- renderPlot({
        
        plot_backtest(sim_data1 =  sim_data_noquar(), 
            sim_data2 = sim_data_quar(), input$input_xaxis)
        
    }) 
}

shinyApp(ui, server)