library(R2WinBUGS); library(mcmcplots); library(ggplot2);library(gridExtra);library(ggpubr);library(tidyverse);library(AHMbook);library(jagsUI);library(rjags);
library(dplyr);library(dbplyr);library(scales);library(Hmisc); library(shinystan); library(rstanarm); library(bayesplot); library(imputeTS); library(FSA);library(zoo)
library(statip)
setwd("C:/Users/cjs18021/OneDrive - University of Connecticut/UConn/Research/Dissertation/Papers/Trout movement")


##simulated data set, 
phiA<-0.660
phiB<-0.821
phiC<-0.834
phiD<-0.854

psiAB<-0.163
psiAC<-0.124
psiAD<-0.135

psiBA<-0.041
psiBC<-0.059
psiBD<-0.031

psiCA<-0.020
psiCB<-0.056
psiCD<-0.040

psiDA<-0.031
psiDB<-0.029
psiDC<-0.049

pA<-0.967
pB<-0.996
pC<-0.777
pD<-0.75

fA<-0.660
fB<-0.822
fC<-0.835
fD<-0.855


n.occasions<-24*2
n.states<-6
n.obs<-6
marked<-matrix(NA,ncol=n.states,nrow=n.occasions)
marked[,1]<-rep(0,n.occasions)
marked[,2]<-rep(0,n.occasions)
marked[,3]<-rep(0,n.occasions)
marked[,4]<-rep(1,n.occasions)
marked[,5]<-rep(0,n.occasions)
marked[,6]<-rep(0,n.occasions)
marked[1,2]<-rep(18)
marked[1,1]<-rep(17)
marked[1,3]<-rep(17)
totrel<-sum(marked)*(n.occasions-1)
PSI.STATE<-array(NA,dim = c(n.states,n.states,totrel,n.occasions-1))
for(i in 1:totrel){
  for(t in 1:(n.occasions-1)){
    PSI.STATE[,,i,t]<-matrix(c(
      fA*phiA*(1-psiAB-psiAC-psiAD), fA*phiA*psiAB                , fA*phiA*psiAC                , fA*phiA*psiAD               , (1-fA), fA*(1-phiA),
      fB*phiB*psiBA                , fB*phiB*(1-psiBA-psiBC-psiBD), fB*phiB*psiBC                , fB*phiB*psiBD               , (1-fB), fB*(1-phiB),
      fC*phiC*psiCA                , fC*phiC*psiCB                , fC*phiC*(1-psiCA-psiCB-psiCD), fC*phiC*psiCD               , (1-fC), fC*(1-phiC),
      fD*phiD*psiDA                , fD*phiD*psiDB                , fD*phiD*psiDC                , fD*phiD*(1-psiDA-psiDB-psiDC),(1-fD), fD*(1-phiD),
      0,0,0,0,1,0, 
      0,0,0,0,0,1),
      nrow = n.states,byrow = TRUE)
  }
}


PSI.OBS<-array(NA,dim = c(n.states,n.obs,totrel,n.occasions-1))
for(i in 1:totrel){
  for(t in (1:n.occasions-1)){
    PSI.OBS[,,i,t]<-matrix(c(
      pA, 0 , 0 , 0 , 0, 1-pA,
      0 , pB, 0 , 0 , 0, 1-pB,
      0 , 0 , pC, 0 , 0, 1-pC,
      0 , 0 , 0 , pD, 0, 1-pD,
      0 , 0 , 0 , 0 , 1, 0   ,
      0 , 0 , 0 , 0 , 0, 1   ),nrow = n.states,byrow = TRUE)
  }
}

simul.ms<-function(PSI.STATE,PSI.OBS,marked,unobservable=NA){
  n.occasions<-dim(PSI.STATE)[4]+1
  CH<-CH.TRUE<-matrix(NA,ncol=n.occasions,nrow=sum(marked))
  mark.occ<-matrix(0,ncol=dim(PSI.STATE)[1],nrow=sum(marked))
  g<-colSums(marked)
  for(s in 1:dim(PSI.STATE)[1]){
    if(g[s]==0) next
    mark.occ[(cumsum(g[1:s])-g[s]+1)[s]:cumsum(g[1:s])[s],s]<-
      rep(1:n.occasions,marked[1:n.occasions,s])
  }
  for(i in 1:sum(marked)){
    for(s in 1:dim(PSI.STATE)[1]){
      if(mark.occ[i,s]==0) next
      first<-mark.occ[i,s]
      CH[i,first]<-s
      CH.TRUE[i,first]<-s
    }
    for(t in (first+1):n.occasions){
      if(first==n.occasions) next
      state<-which(rmultinom(1,1,PSI.STATE[CH.TRUE[i,t-1],,
                                           i,t-1])==1)
      CH.TRUE[i,t]<-state
      event<-which(rmultinom(1,1,PSI.OBS[CH.TRUE[i,t],,i,
                                         t-1])==1)
      CH[i,t]<-event
    }
  }
  CH[is.na(CH)]<-0
  CH[CH==dim(PSI.STATE)[1]]<-0
  CH[CH==unobservable]<-0
  id<-numeric(0)
  for(i in 1:dim(CH)[1]){
    z<-min(which(CH[i,]!=0))
    ifelse(z==dim(CH)[2],id<-c(id,i),id<-c(id))
  }
  return(list(CH=CH[-id,],CH.TRUE=CH.TRUE[-id,]))
}

sim<-simul.ms(PSI.STATE,PSI.OBS,marked)
CH<-sim$CH

get.first<-function(x)min(which(x!=0))
f<-apply(CH,1,get.first)
rCH<-CH
rCH[rCH==0]<-6

simch <- rCH[1:52,]


#--------------------Functions to be used----------------------

# identify the occasion of first capture
get.first <- function(x) min(which(x!=6))

## identify the occasion on which mortality occurred
## if mortality did not occur, assign the last occasion
get.last <- function(x){
  if (sum(x, na.rm=TRUE) > 0) max(which(x==1))
  else length(x)
}

known.state.ms <- function(ms, notseen){
  # notseen: label for ‘not seen’
  state <- ms
  state[state==notseen] <- NA
  for (i in 1:dim(ms)[1]){
    m <- min(which(!is.na(state[i,])))
    state[i,m] <- NA
  }
  return(state)
}

ms.init.z  <- function(ms, known.z, permemig, notseen){ #capt hist, known z (data), not seen
  state <- ms
  state[state==permemig] <- notseen
  state[state==notseen] <- NA    # if not seen put NA
  
  for(i in 1:dim(state)[1]){ #Do this for every row
    m <- min(which(!is.na(state[i,])))   #identify the first occasion not NA
    
    if(any(!is.na(state[i,1:dim(state)[2]-1]))){
      state[i,dim(state)[2]] <- max(state[i,],na.rm=TRUE) # populate last column as na.interpolation needs at least two values
      state[i,] <- ceiling(na.interpolation(state[i,])) # install "imputeTS" package
    } #if
    
    state[i,1:m] <- NA  ## NA until the first occation
  } #i
  
  state[!is.na(known.z)] <- NA   ## don't suuply initial values when z is known (data)
  
  return(state)
} 

#--------------------read in and format data----------------------
rCH <- simch 
firstOcc <- apply(rCH, 1, get.first)
n.occasions=dim(rCH)[2]
nind=dim(rCH)[1]
n.states=4
summary(covs)

#----bring in covariates
covs<-read.csv("covs_11-6.csv",header = TRUE)
covs <- covs[,c(5:12)]
covs <- cbind(apply(covs, 2, scale, scale=T), covs)
Pred <- covs[,1]
DZoneD <- covs[,2]
CVZoneD <- covs[,3]
Tdiff <- covs[,4]
TZoneA <- covs[,5]
TZoneB <- covs[,6]
TZoneC <- covs[,7]
TZoneD <- covs[,8]

library(Hmisc)
##covs <- as.matrix(covs)
#res <- rcorr(covs, type="spearman")
#res2 <- as.data.frame(flattenCorrMatrix(res$r, res$P))
#str(res2)
library(corrplot)
#corrplot(res2$cor)
#corrplot(cor(covs_st[1:8]))

cov.seq <-  seq(min(Pred),max(Pred),length.out=100)
cov.num <- length(cov.seq)

cat(file="statespace.txt","
    model{
    #------------------Priors and constraints--------------------------------
        pA~dunif(0,1)                                                       # Priors for recapture probabilities in each zone
        pB~dunif(0,1)
        pC~dunif(0,1)
        pD~dunif(0,1)
       
        sA~dunif(0,1)                                                       # Priors for survival probabilities in each zone
        sB~dunif(0,1)
        sC~dunif(0,1)
        sD~dunif(0,1)
        

         fA ~ dunif(0,1)                                                # Priors for site fidelity probability (1-prob of emigration from the zone)
         fB ~ dunif(0,1)  
         fC ~ dunif(0,1)  
         fD ~ dunif(0,1)



  for (i in 1:4){
         wA[i] ~ dbern(.5)
         wB[i] ~ dbern(.5)
         wC[i] ~ dbern(.5)
         wD[i] ~ dbern(.5)
  }


  for (t in 1:(n.occasions-1)){
    for (i in 1:4){
       A[i,t] <- exp(muA[i] + wA[i]*betaA[i]*x[t])
       psiA[i,t] <- A[i,t]/sum(A[,t])
       
       B[i,t] <- exp(muB[i] + wB[i]*betaB[i]*x[t])
       psiB[i,t] <- B[i,t]/sum(B[,t])
       
       C[i,t] <- exp(muC[i] + wC[i]*betaC[i]*x[t])
       psiC[i,t] <- C[i,t]/sum(C[,t])
       
       D[i,t] <- exp(muD[i] + wD[i]*betaD[i]*x[t])
       psiD[i,t] <- D[i,t]/sum(D[,t])
       }
  }

   for(i in 1:4){
      muA[i] ~ dt(0, 1/1.566^2, 7.763)
      betaA[i] ~ dt(0, 1/1.566^2, 7.763)
      
      muB[i] ~ dt(0, 1/1.566^2, 7.763)
      betaB[i] ~ dt(0, 1/1.566^2, 7.763)
      
      muC[i] ~ dt(0, 1/1.566^2, 7.763)
      betaC[i] ~ dt(0, 1/1.566^2, 7.763)
      
      muD[i] ~ dt(0, 1/1.566^2, 7.763)
      betaD[i] ~ dt(0, 1/1.566^2, 7.763)
 }


  #------------------predicted transitions for plotting-----------------------------
   for(r in 1:cov.num){
      for(i in 1:4){
          pred.A[i,r] <- exp(muA[i] + wA[i]*betaA[i]*cov.seq[r])
          pred.psiA[i,r] <- pred.A[i,r]/sum(pred.A[,r])
          
          pred.B[i,r] <- exp(muB[i] + wB[i]*betaB[i]*cov.seq[r])
          pred.psiB[i,r] <- pred.B[i,r]/sum(pred.B[,r])
                    
          pred.C[i,r] <- exp(muC[i] + wC[i]*betaC[i]*cov.seq[r])
          pred.psiC[i,r] <- pred.C[i,r]/sum(pred.C[,r])
                    
          pred.D[i,r] <- exp(muD[i] + wD[i]*betaD[i]*cov.seq[r])
          pred.psiD[i,r] <- pred.D[i,r]/sum(pred.D[,r])
 }
}
 
  #------------------Define state-transitions and observation matrices-----------------------------
    for(i in 1:nind){
        for(t in f[i]:(n.occasions-1)){                                     #define probabilities of state S (t+1) given S(t)
            ps[1,i,t,1]<- fA*sA*psiA[4,t]       #Zone A to Zone A
            ps[1,i,t,2]<- fA*sA*psiA[1,t]       #Zone A to Zone B
            ps[1,i,t,3]<- fA*sA*psiA[2,t]       #Zone A to Zone C
            ps[1,i,t,4]<- fA*sA*psiA[3,t]       #Zone A to Zone D
            ps[1,i,t,5]<- 1-fA                       #Emigrate
            ps[1,i,t,6]<- fA*(1-sA)             #Dead
            
            ps[2,i,t,1]<- fB*sB*psiB[1,t]       #Zone B to Zone A
            ps[2,i,t,2]<- fB*sB*psiB[4,t]       #Zone B to Zone B
            ps[2,i,t,3]<- fB*sB*psiB[2,t]       #Zone B to Zone C    
            ps[2,i,t,4]<- fB*sB*psiB[3,t]       #Zone B to Zone D 
            ps[2,i,t,5]<- 1-fB                       #Emigrate
            ps[2,i,t,6]<- fB*(1-sB)              #Dead
            
            ps[3,i,t,1]<- fC*sC*psiC[1,t]       #Zone C to Zone A
            ps[3,i,t,2]<- fC*sC*psiC[2,t]       #Zone C to Zone B
            ps[3,i,t,3]<- fC*sC*psiC[4,t]       #Zone C to Zone C
            ps[3,i,t,4]<- fC*sC*psiC[3,t]       #Zone C to Zone D
            ps[3,i,t,5]<- 1-fC                     #Emigrate
            ps[3,i,t,6]<- fC*(1-sC)             #Dead
            
            ps[4,i,t,1]<- fD*sD*psiD[1,t]       #Zone D to Zone A
            ps[4,i,t,2]<- fD*sD*psiD[2,t]       #Zone D to Zone B
            ps[4,i,t,3]<- fD*sD*psiD[3,t]       #Zone D to Zone C
            ps[4,i,t,4]<- fD*sD*psiD[4,t]       #Zone D to Zone D
            ps[4,i,t,5]<- 1-fD
            ps[4,i,t,6]<- fD*(1-sD)
            
            ps[5,i,t,1]<- 0
            ps[5,i,t,2]<- 0
            ps[5,i,t,3]<- 0
            ps[5,i,t,4]<- 0
            ps[5,i,t,5]<- 1
            ps[5,i,t,6]<- 0
            
            ps[6,i,t,1]<- 0
            ps[6,i,t,2]<- 0
            ps[6,i,t,3]<- 0
            ps[6,i,t,4]<- 0
            ps[6,i,t,5]<- 0
            ps[6,i,t,6]<- 1
                                                                            #define probabilities of 0(t) given S(t)
            po[1,i,t,1]<- pA
            po[1,i,t,2]<- 0
            po[1,i,t,3]<- 0
            po[1,i,t,4]<- 0
            po[1,i,t,5]<- 0
            po[1,i,t,6]<- 1-pA
            
            po[2,i,t,1]<- 0
            po[2,i,t,2]<- pB
            po[2,i,t,3]<- 0
            po[2,i,t,4]<- 0
            po[2,i,t,5]<- 0
            po[2,i,t,6]<- 1-pB
           
            po[3,i,t,1]<- 0
            po[3,i,t,2]<- 0
            po[3,i,t,3]<- pC
            po[3,i,t,4]<- 0
            po[3,i,t,5]<- 0
            po[3,i,t,6]<- 1-pC
           
            po[4,i,t,1]<- 0
            po[4,i,t,2]<- 0
            po[4,i,t,3]<- 0
            po[4,i,t,4]<- pD
            po[4,i,t,5]<- 0
            po[4,i,t,6]<- 1-pD
            
            po[5,i,t,1]<- 0
            po[5,i,t,2]<- 0
            po[5,i,t,3]<- 0
            po[5,i,t,4]<- 0
            po[5,i,t,5]<- 1
            po[5,i,t,6]<- 0
            
            po[6,i,t,1]<- 0
            po[6,i,t,2]<- 0
            po[6,i,t,3]<- 0
            po[6,i,t,4]<- 0
            po[6,i,t,5]<- 0
            po[6,i,t,6]<- 1
       }
    }
  #-----------------------------------Likelihood-----------------------------------
    for(i in 1:nind){
       z[i,f[i]]<-y[i,f[i]]                                        #define latent state at first glance
           for (t in (f[i]+1):n.occasions){
                      z[i,t]~dcat(ps[z[i,t-1],i,t-1,])                  #state process: draw S(t) given S(t-1)
                      y[i,t]~dcat(po[z[i,t],i,t-1,])                    #observation process: draw 0(t) given S(t)
                      }
                }
  #-----------------------------Derived quantities--------------------------------
          for (i in 1:(4)){
             psiA.mean[i] <- mean(psiA[i,])
             psiB.mean[i] <- mean(psiB[i,])
             psiC.mean[i] <- mean(psiC[i,])
             psiD.mean[i] <- mean(psiD[i,])
            }

        }
    ")

rCH
known.z <- known.state.ms(rCH,6)
init.z <- ms.init.z(rCH, known.z, 5, 6) 

str(rCH); str(known.z); str(init.z)


####################################################################
###################   Predation
####################################################################
bugs.data<-list(y=rCH, f=firstOcc, n.occasions=dim(rCH)[2], nind=dim(rCH)[1], z=known.z,
                cov.seq = cov.seq, cov.num=cov.num, x=Pred)

inits<-function(){list(muA = runif(4,-1,1),
                       muB = runif(4,-1,1),
                       muC = runif(4,-1,1),
                       muD = runif(4,-1,1),
                       wA = rbinom(4, 1, 0.5),
                       wB = rbinom(4, 1, 0.5),
                       wC = rbinom(4, 1, 0.5),
                       wD = rbinom(4, 1, 0.5),
                       betaA = runif(4,-1,1),
                       betaB = runif(4,-1,1),
                       betaC = runif(4,-1,1),
                       betaD = runif(4,-1,1),
                       pA=runif(1,0.5,1),
                       pB=runif(1,0.5,1),
                       pC=runif(1,0.5,1),
                       pD=runif(1,0.5,1),
                       z=init.z)}

parameters<-c("wA","wB","wC","wD",
              "muA","muB","muC","muD",
              "betaA","betaB","betaC","betaD",
              "pred.psiA","pred.psiB","pred.psiC","pred.psiD",
              "sA","sB","sC","sD", 
              "fA","fB","fC", "fD",
              "psiA","psiB","psiC","psiD", 
              "pA","pB","pC","pD", 
              "psiA.mean", "psiB.mean","psiC.mean","psiD.mean")
ni<-50000
nt<-50
nb<-20000
nc<-3
na <- 10000

ms <- jags(data=bugs.data, inits = inits, parameters.to.save = parameters, 
           model.file="statespace.txt", n.adapt= na, n.chains=nc, n.thin=nt, n.iter=ni, n.burnin=nb, parallel=TRUE, seed=53)

print(ms, digits = 3)
ms_output_pred <- as.data.frame(jags.View(ms)) 
write.csv(ms_output_pred, "ms_output_pred_1hr_simulated_data.csv")

####################################################################
###################   Temperature differential
####################################################################
cov.seq <-  seq(min(Tdiff),max(Tdiff),length.out=100)
cov.num <- length(cov.seq)


bugs.data<-list(y=rCH, f=firstOcc, n.occasions=dim(rCH)[2], nind=dim(rCH)[1], z=known.z,
                cov.seq = cov.seq, cov.num=cov.num, x=Tdiff)

inits<-function(){list(muA = runif(4,-1,1),
                       muB = runif(4,-1,1),
                       muC = runif(4,-1,1),
                       muD = runif(4,-1,1),
                       wA = rbinom(4, 1, 0.5),
                       wB = rbinom(4, 1, 0.5),
                       wC = rbinom(4, 1, 0.5),
                       wD = rbinom(4, 1, 0.5),
                       betaA = runif(4,-1,1),
                       betaB = runif(4,-1,1),
                       betaC = runif(4,-1,1),
                       betaD = runif(4,-1,1),
                       pA=runif(1,0.5,1),
                       pB=runif(1,0.5,1),
                       pC=runif(1,0.5,1),
                       pD=runif(1,0.5,1),
                       z=init.z)}

parameters<-c("wA","wB","wC","wD",
              "muA","muB","muC","muD",
              "betaA","betaB","betaC","betaD",
              "pred.psiA","pred.psiB","pred.psiC","pred.psiD",
              "sA","sB","sC","sD", 
              "fA","fB","fC", "fD",
              "psiA","psiB","psiC","psiD", 
              "pA","pB","pC","pD", 
              "psiA.mean", "psiB.mean","psiC.mean","psiD.mean")
ni<-50000
nt<-50
nb<-20000
nc<-3
na <- 10000

ms <- jags(data=bugs.data, inits = inits, parameters.to.save = parameters, 
           model.file="statespace.txt", n.adapt= na, n.chains=nc, n.thin=nt, n.iter=ni, n.burnin=nb, parallel=TRUE, seed=53)

print(ms, digits = 3)
ms_output_tdiff <- as.data.frame(jags.View(ms)) 
write.csv(ms_output_tdiff, "ms_output_tdiff_1hr_simulated_data.csv")

####################################################################
###################   Temp Zone A
####################################################################
cov.seq <-  seq(min(TZoneA),max(TZoneA),length.out=100)
cov.num <- length(cov.seq)


bugs.data<-list(y=rCH, f=firstOcc, n.occasions=dim(rCH)[2], nind=dim(rCH)[1], z=known.z,
                cov.seq = cov.seq, cov.num=cov.num, x=TZoneA)

inits<-function(){list(muA = runif(4,-1,1),
                       muB = runif(4,-1,1),
                       muC = runif(4,-1,1),
                       muD = runif(4,-1,1),
                       wA = rbinom(4, 1, 0.5),
                       wB = rbinom(4, 1, 0.5),
                       wC = rbinom(4, 1, 0.5),
                       wD = rbinom(4, 1, 0.5),
                       betaA = runif(4,-1,1),
                       betaB = runif(4,-1,1),
                       betaC = runif(4,-1,1),
                       betaD = runif(4,-1,1),
                       pA=runif(1,0.5,1),
                       pB=runif(1,0.5,1),
                       pC=runif(1,0.5,1),
                       pD=runif(1,0.5,1),
                       z=init.z)}

parameters<-c("wA","wB","wC","wD",
              "muA","muB","muC","muD",
              "betaA","betaB","betaC","betaD",
              "pred.psiA","pred.psiB","pred.psiC","pred.psiD",
              "sA","sB","sC","sD", 
              "fA","fB","fC", "fD",
              "psiA","psiB","psiC","psiD", 
              "pA","pB","pC","pD", 
              "psiA.mean", "psiB.mean","psiC.mean","psiD.mean")
ni<-50000
nt<-50
nb<-20000
nc<-3
na <- 10000

ms <- jags(data=bugs.data, inits = inits, parameters.to.save = parameters, 
           model.file="statespace.txt", n.adapt= na, n.chains=nc, n.thin=nt, n.iter=ni, n.burnin=nb, parallel=TRUE, seed=53)

print(ms, digits = 3)
ms_output_TZoneA <- as.data.frame(jags.View(ms)) 
write.csv(ms_output_TZoneA, "ms_output_TZoneA_1hr_simulated_data.csv")

####################################################################
###################   Temp Zone B
####################################################################
cov.seq <-  seq(min(TZoneB),max(TZoneB),length.out=100)
cov.num <- length(cov.seq)


bugs.data<-list(y=rCH, f=firstOcc, n.occasions=dim(rCH)[2], nind=dim(rCH)[1], z=known.z,
                cov.seq = cov.seq, cov.num=cov.num, x=TZoneB)

inits<-function(){list(muA = runif(4,-1,1),
                       muB = runif(4,-1,1),
                       muC = runif(4,-1,1),
                       muD = runif(4,-1,1),
                       wA = rbinom(4, 1, 0.5),
                       wB = rbinom(4, 1, 0.5),
                       wC = rbinom(4, 1, 0.5),
                       wD = rbinom(4, 1, 0.5),
                       betaA = runif(4,-1,1),
                       betaB = runif(4,-1,1),
                       betaC = runif(4,-1,1),
                       betaD = runif(4,-1,1),
                       pA=runif(1,0.5,1),
                       pB=runif(1,0.5,1),
                       pC=runif(1,0.5,1),
                       pD=runif(1,0.5,1),
                       z=init.z)}

parameters<-c("wA","wB","wC","wD",
              "muA","muB","muC","muD",
              "betaA","betaB","betaC","betaD",
              "pred.psiA","pred.psiB","pred.psiC","pred.psiD",
              "sA","sB","sC","sD", 
              "fA","fB","fC", "fD",
              "psiA","psiB","psiC","psiD", 
              "pA","pB","pC","pD", 
              "psiA.mean", "psiB.mean","psiC.mean","psiD.mean")
ni<-50000
nt<-50
nb<-20000
nc<-3
na <- 10000

ms <- jags(data=bugs.data, inits = inits, parameters.to.save = parameters, 
           model.file="statespace.txt", n.adapt= na, n.chains=nc, n.thin=nt, n.iter=ni, n.burnin=nb, parallel=TRUE, seed=53)

print(ms, digits = 3)
ms_output_TZoneB <- as.data.frame(jags.View(ms)) 
write.csv(ms_output_TZoneB, "ms_output_TZoneB_1hr_simulated_data.csv")

####################################################################
###################   Temp Zone C
####################################################################
cov.seq <-  seq(min(TZoneC),max(TZoneC),length.out=100)
cov.num <- length(cov.seq)


bugs.data<-list(y=rCH, f=firstOcc, n.occasions=dim(rCH)[2], nind=dim(rCH)[1], z=known.z,
                cov.seq = cov.seq, cov.num=cov.num, x=TZoneC)

inits<-function(){list(muA = runif(4,-1,1),
                       muB = runif(4,-1,1),
                       muC = runif(4,-1,1),
                       muD = runif(4,-1,1),
                       wA = rbinom(4, 1, 0.5),
                       wB = rbinom(4, 1, 0.5),
                       wC = rbinom(4, 1, 0.5),
                       wD = rbinom(4, 1, 0.5),
                       betaA = runif(4,-1,1),
                       betaB = runif(4,-1,1),
                       betaC = runif(4,-1,1),
                       betaD = runif(4,-1,1),
                       pA=runif(1,0.5,1),
                       pB=runif(1,0.5,1),
                       pC=runif(1,0.5,1),
                       pD=runif(1,0.5,1),
                       z=init.z)}

parameters<-c("wA","wB","wC","wD",
              "muA","muB","muC","muD",
              "betaA","betaB","betaC","betaD",
              "pred.psiA","pred.psiB","pred.psiC","pred.psiD",
              "sA","sB","sC","sD", 
              "fA","fB","fC", "fD",
              "psiA","psiB","psiC","psiD", 
              "pA","pB","pC","pD", 
              "psiA.mean", "psiB.mean","psiC.mean","psiD.mean")
ni<-50000
nt<-50
nb<-20000
nc<-3
na <- 10000

ms <- jags(data=bugs.data, inits = inits, parameters.to.save = parameters, 
           model.file="statespace.txt", n.adapt= na, n.chains=nc, n.thin=nt, n.iter=ni, n.burnin=nb, parallel=TRUE, seed=53)

print(ms, digits = 3)
ms_output_TZoneC <- as.data.frame(jags.View(ms)) 
write.csv(ms_output_TZoneC, "ms_output_TZoneC_1hr_simulated_data.csv")

####################################################################
###################   Temp Zone D
####################################################################
cov.seq <-  seq(min(TZoneD),max(TZoneD),length.out=100)
cov.num <- length(cov.seq)


bugs.data<-list(y=rCH, f=firstOcc, n.occasions=dim(rCH)[2], nind=dim(rCH)[1], z=known.z,
                cov.seq = cov.seq, cov.num=cov.num, x=TZoneD)

inits<-function(){list(muA = runif(4,-1,1),
                       muB = runif(4,-1,1),
                       muC = runif(4,-1,1),
                       muD = runif(4,-1,1),
                       wA = rbinom(4, 1, 0.5),
                       wB = rbinom(4, 1, 0.5),
                       wC = rbinom(4, 1, 0.5),
                       wD = rbinom(4, 1, 0.5),
                       betaA = runif(4,-1,1),
                       betaB = runif(4,-1,1),
                       betaC = runif(4,-1,1),
                       betaD = runif(4,-1,1),
                       pA=runif(1,0.5,1),
                       pB=runif(1,0.5,1),
                       pC=runif(1,0.5,1),
                       pD=runif(1,0.5,1),
                       z=init.z)}

parameters<-c("wA","wB","wC","wD",
              "muA","muB","muC","muD",
              "betaA","betaB","betaC","betaD",
              "pred.psiA","pred.psiB","pred.psiC","pred.psiD",
              "sA","sB","sC","sD", 
              "fA","fB","fC", "fD",
              "psiA","psiB","psiC","psiD", 
              "pA","pB","pC","pD", 
              "psiA.mean", "psiB.mean","psiC.mean","psiD.mean")
ni<-50000
nt<-50
nb<-20000
nc<-3
na <- 10000

ms <- jags(data=bugs.data, inits = inits, parameters.to.save = parameters, 
           model.file="statespace.txt", n.adapt= na, n.chains=nc, n.thin=nt, n.iter=ni, n.burnin=nb, parallel=TRUE, seed=53)

print(ms, digits = 3)
ms_output_TZoneD <- as.data.frame(jags.View(ms)) 
write.csv(ms_output_TZoneD, "ms_output_TZoneD_1hr_simulated_data.csv")

####################################################################
###################   Dis Zone D
####################################################################
cov.seq <-  seq(min(DZoneD),max(DZoneD),length.out=100)
cov.num <- length(cov.seq)


bugs.data<-list(y=rCH, f=firstOcc, n.occasions=dim(rCH)[2], nind=dim(rCH)[1], z=known.z,
                cov.seq = cov.seq, cov.num=cov.num, x=DZoneD)

inits<-function(){list(muA = runif(4,-1,1),
                       muB = runif(4,-1,1),
                       muC = runif(4,-1,1),
                       muD = runif(4,-1,1),
                       wA = rbinom(4, 1, 0.5),
                       wB = rbinom(4, 1, 0.5),
                       wC = rbinom(4, 1, 0.5),
                       wD = rbinom(4, 1, 0.5),
                       betaA = runif(4,-1,1),
                       betaB = runif(4,-1,1),
                       betaC = runif(4,-1,1),
                       betaD = runif(4,-1,1),
                       pA=runif(1,0.5,1),
                       pB=runif(1,0.5,1),
                       pC=runif(1,0.5,1),
                       pD=runif(1,0.5,1),
                       z=init.z)}

parameters<-c("wA","wB","wC","wD",
              "muA","muB","muC","muD",
              "betaA","betaB","betaC","betaD",
              "pred.psiA","pred.psiB","pred.psiC","pred.psiD",
              "sA","sB","sC","sD", 
              "fA","fB","fC", "fD",
              "psiA","psiB","psiC","psiD", 
              "pA","pB","pC","pD", 
              "psiA.mean", "psiB.mean","psiC.mean","psiD.mean")
ni<-50000
nt<-50
nb<-20000
nc<-3
na <- 10000

ms <- jags(data=bugs.data, inits = inits, parameters.to.save = parameters, 
           model.file="statespace.txt", n.adapt= na, n.chains=nc, n.thin=nt, n.iter=ni, n.burnin=nb, parallel=TRUE, seed=53)

print(ms, digits = 3)
ms_output_DZoneD <- as.data.frame(jags.View(ms)) 
write.csv(ms_output_DZoneD, "ms_output_DZoneD_1hr_simulated_data.csv")

####################################################################
###################   CV Zone D
####################################################################
cov.seq <-  seq(min(CVZoneD),max(CVZoneD),length.out=100)
cov.num <- length(cov.seq)


bugs.data<-list(y=rCH, f=firstOcc, n.occasions=dim(rCH)[2], nind=dim(rCH)[1], z=known.z,
                cov.seq = cov.seq, cov.num=cov.num, x=CVZoneD)

inits<-function(){list(muA = runif(4,-1,1),
                       muB = runif(4,-1,1),
                       muC = runif(4,-1,1),
                       muD = runif(4,-1,1),
                       wA = rbinom(4, 1, 0.5),
                       wB = rbinom(4, 1, 0.5),
                       wC = rbinom(4, 1, 0.5),
                       wD = rbinom(4, 1, 0.5),
                       betaA = runif(4,-1,1),
                       betaB = runif(4,-1,1),
                       betaC = runif(4,-1,1),
                       betaD = runif(4,-1,1),
                       pA=runif(1,0.5,1),
                       pB=runif(1,0.5,1),
                       pC=runif(1,0.5,1),
                       pD=runif(1,0.5,1),
                       z=init.z)}

parameters<-c("wA","wB","wC","wD",
              "muA","muB","muC","muD",
              "betaA","betaB","betaC","betaD",
              "pred.psiA","pred.psiB","pred.psiC","pred.psiD",
              "sA","sB","sC","sD", 
              "fA","fB","fC", "fD",
              "psiA","psiB","psiC","psiD", 
              "pA","pB","pC","pD", 
              "psiA.mean", "psiB.mean","psiC.mean","psiD.mean")
ni<-50000
nt<-50
nb<-20000
nc<-3
na <- 10000

ms <- jags(data=bugs.data, inits = inits, parameters.to.save = parameters, 
           model.file="statespace.txt", n.adapt= na, n.chains=nc, n.thin=nt, n.iter=ni, n.burnin=nb, parallel=TRUE, seed=53)

print(ms, digits = 3)
ms_output_CVZoneD <- as.data.frame(jags.View(ms)) 
write.csv(ms_output_CVZoneD, "ms_output_CVZoneD_1hr.csv") 



####################################################################
###################  just time dependency
####################################################################

bugs.data<-list(y=rCH, f=firstOcc, n.occasions=dim(rCH)[2], nind=dim(rCH)[1], z=known.z)

cat(file="statespace.txt","
    model{
    #------------------Priors and constraints--------------------------------
        pA~dunif(0,1)                                                       # Priors for recapture probabilities in each zone
        pB~dunif(0,1)
        pC~dunif(0,1)
        pD~dunif(0,1)
        
        
  for (t in 1:(n.occasions-1)){
         sA[t]~dunif(0,1)                                                     #priors for survival prob in zones A, B, C, D
         sB[t]~dunif(0,1)
         sC[t]~dunif(0,1)
         sD[t]~dunif(0,1)
         
         fA[t] ~ dunif(0,1)                                                # Priors for site fidelity probability (1-prob of emigration from the zone)
         fB[t] ~ dunif(0,1)  
         fC[t] ~ dunif(0,1)  
         fD[t] ~ dunif(0,1)


  #-----------------Movement:normalize all but one--------------------------------------------------
    for(i in 1:3){
        lpsiA[t,i]~dnorm(0,0.001)                                             #transitions
        lpsiB[t,i]~dnorm(0,0.001)
        lpsiC[t,i]~dnorm(0,0.001)
        lpsiD[t,i]~dnorm(0,0.001)
      }

    for(i in 1:3){
        psiA[t,i]<-exp(lpsiA[t,i])/(1+exp(lpsiA[t,1])+exp(lpsiA[t,2])+exp(lpsiA[t,3]))        #constrain transitions such that the sum to 1
        psiB[t,i]<-exp(lpsiB[t,i])/(1+exp(lpsiB[t,1])+exp(lpsiB[t,2])+exp(lpsiB[t,3]))
        psiC[t,i]<-exp(lpsiC[t,i])/(1+exp(lpsiC[t,1])+exp(lpsiC[t,2])+exp(lpsiC[t,3]))
        psiD[t,i]<-exp(lpsiD[t,i])/(1+exp(lpsiD[t,1])+exp(lpsiD[t,2])+exp(lpsiD[t,3]))
   }
    psiA[t,4] <- 1-psiA[t,1]-psiA[t,2]-psiA[t,3]                                         
    psiB[t,4] <- 1-psiB[t,1]-psiB[t,2]-psiB[t,3]
    psiC[t,4] <- 1-psiC[t,1]-psiC[t,2]-psiC[t,3]
    psiD[t,4] <- 1-psiD[t,1]-psiD[t,2]-psiD[t,3]
  } 
  
  #------------------Define state-transitions and observation matrices-----------------------------
    for(i in 1:nind){
        for(t in f[i]:(n.occasions-1)){                                     #define probabilities of state S (t+1) given S(t)
            ps[1,i,t,1]<- fA[t]*sA[t]*psiA[t,4]       #Zone A to Zone A
            ps[1,i,t,2]<- fA[t]*sA[t]*psiA[t,1]       #Zone A to Zone B
            ps[1,i,t,3]<- fA[t]*sA[t]*psiA[t,2]       #Zone A to Zone C
            ps[1,i,t,4]<- fA[t]*sA[t]*psiA[t,3]       #Zone A to Zone D
            ps[1,i,t,5]<- 1-fA[t]                       #Emigrate
            ps[1,i,t,6]<- fA[t]*(1-sA[t])             #Dead
            
            ps[2,i,t,1]<- fB[t]*sB[t]*psiB[t,1]       #Zone B to Zone A
            ps[2,i,t,2]<- fB[t]*sB[t]*psiB[t,4]       #Zone B to Zone B
            ps[2,i,t,3]<- fB[t]*sB[t]*psiB[t,2]       #Zone B to Zone C    
            ps[2,i,t,4]<- fB[t]*sB[t]*psiB[t,3]       #Zone B to Zone D 
            ps[2,i,t,5]<- 1-fB[t]                       #Emigrate
            ps[2,i,t,6]<- fB[t]*(1-sB[t])              #Dead
            
            ps[3,i,t,1]<- fC[t]*sC[t]*psiC[t,1]       #Zone C to Zone A
            ps[3,i,t,2]<- fC[t]*sC[t]*psiC[t,2]       #Zone C to Zone B
            ps[3,i,t,3]<- fC[t]*sC[t]*psiC[t,4]       #Zone C to Zone C
            ps[3,i,t,4]<- fC[t]*sC[t]*psiC[t,3]       #Zone C to Zone D
            ps[3,i,t,5]<- 1-fC[t]                       #Emigrate
            ps[3,i,t,6]<- fC[t]*(1-sC[t])             #Dead
            
            ps[4,i,t,1]<- fD[t]*sD[t]*psiD[t,1]       #Zone D to Zone A
            ps[4,i,t,2]<- fD[t]*sD[t]*psiD[t,2]       #Zone D to Zone B
            ps[4,i,t,3]<- fD[t]*sD[t]*psiD[t,3]       #Zone D to Zone C
            ps[4,i,t,4]<- fD[t]*sD[t]*psiD[t,4]       #Zone D to Zone D
            ps[4,i,t,5]<- 1-fD[t]
            ps[4,i,t,6]<- fD[t]*(1-sD[t])
            
            ps[5,i,t,1]<- 0
            ps[5,i,t,2]<- 0
            ps[5,i,t,3]<- 0
            ps[5,i,t,4]<- 0
            ps[5,i,t,5]<- 1
            ps[5,i,t,6]<- 0
            
            ps[6,i,t,1]<- 0
            ps[6,i,t,2]<- 0
            ps[6,i,t,3]<- 0
            ps[6,i,t,4]<- 0
            ps[6,i,t,5]<- 0
            ps[6,i,t,6]<- 1
                                                                            #define probabilities of 0(t) given S(t)
            po[1,i,t,1]<- pA
            po[1,i,t,2]<- 0
            po[1,i,t,3]<- 0
            po[1,i,t,4]<- 0
            po[1,i,t,5]<- 0
            po[1,i,t,6]<- 1-pA
            
            po[2,i,t,1]<- 0
            po[2,i,t,2]<- pB
            po[2,i,t,3]<- 0
            po[2,i,t,4]<- 0
            po[2,i,t,5]<- 0
            po[2,i,t,6]<- 1-pB
           
            po[3,i,t,1]<- 0
            po[3,i,t,2]<- 0
            po[3,i,t,3]<- pC
            po[3,i,t,4]<- 0
            po[3,i,t,5]<- 0
            po[3,i,t,6]<- 1-pC
           
            po[4,i,t,1]<- 0
            po[4,i,t,2]<- 0
            po[4,i,t,3]<- 0
            po[4,i,t,4]<- pD
            po[4,i,t,5]<- 0
            po[4,i,t,6]<- 1-pD
            
            po[5,i,t,1]<- 0
            po[5,i,t,2]<- 0
            po[5,i,t,3]<- 0
            po[5,i,t,4]<- 0
            po[5,i,t,5]<- 1
            po[5,i,t,6]<- 0
            
            po[6,i,t,1]<- 0
            po[6,i,t,2]<- 0
            po[6,i,t,3]<- 0
            po[6,i,t,4]<- 0
            po[6,i,t,5]<- 0
            po[6,i,t,6]<- 1
       }
    }
  #-----------------------------------Likelihood-----------------------------------
    for(i in 1:nind){
       z[i,f[i]]<-y[i,f[i]]                                        #define latent state at first glance
           for (t in (f[i]+1):n.occasions){
                      z[i,t]~dcat(ps[z[i,t-1],i,t-1,])                  #state process: draw S(t) given S(t-1)
                      y[i,t]~dcat(po[z[i,t],i,t-1,])                    #observation process: draw 0(t) given S(t)
                      }
                }
  #-----------------------------Derived quantities--------------------------------
          for (i in 1:(4)){
             psiA.mean[i] <- mean(psiA[,i])
             psiB.mean[i] <- mean(psiB[,i])
             psiC.mean[i] <- mean(psiC[,i])
             psiD.mean[i] <- mean(psiD[,i])
            }

             sA.mean <- mean(sA)
             sB.mean <- mean(sB)
             sC.mean <- mean(sC)
             sD.mean <- mean(sD)
             
             fA.mean <- mean(fA)
             fB.mean <- mean(fB)
             fC.mean <- mean(fC)
             fD.mean <- mean(fD)

        }
    ")


inits<-function(){list(sA=runif((n.occasions-1),0,1),
                       sB=runif((n.occasions-1),0,1),
                       sC=runif((n.occasions-1),0,1),
                       sD=runif((n.occasions-1),0,1),
                       lpsiA=array(rnorm((n.occasions-1),3), dim = c((n.occasions-1),3)),
                       lpsiB=array(rnorm((n.occasions-1),3), dim = c((n.occasions-1),3)),
                       lpsiC=array(rnorm((n.occasions-1),3), dim = c((n.occasions-1),3)),
                       lpsiD=array(rnorm((n.occasions-1),3), dim = c((n.occasions-1),3)),
                       pA=runif(1,0,1),
                       pB=runif(1,0,1),
                       pC=runif(1,0,1),
                       pD=runif(1,0,1),
                       z=init.z)}

parameters<-c("psiA.mean", "psiB.mean","psiC.mean","psiD.mean",
              "sA.mean","sB.mean","sC.mean","sD.mean",
              "fA.mean","fB.mean","fC.mean","fD.mean",
              "sA","sB","sC","sD", 
              "psiA","psiB","psiC","psiD", 
              "pA","pB","pC","pD", 
              "fA","fB","fC", "fD")
ni<-50000
nt<-50
nb<-20000
nc<-3
na <- 10000

ms <- jags(data=bugs.data, inits = inits, parameters.to.save = parameters, 
           model.file="statespace.txt", n.adapt= na, n.chains=nc, n.thin=nt, n.iter=ni, n.burnin=nb, parallel=TRUE, seed=53)


print(ms, digits = 3)
ms_output_timedep <- as.data.frame(jags.View(ms)) 
write.csv(ms_output_timedep, "ms_output_timedep.csv") 



#####################################################################################################################
############# graphing
#####################################################################################################################


ms.mod <- read.csv("ms_output_DZoneD_1hr_simulated_data_mod11-7.csv")
head(ms.mod)
DZoneD <- subset(ms.mod, param == "Covariate effect")
head(DZoneD)


(Fig.psi.pred <- ggplot(DZoneD, aes(x=DZoneD, y=mean, fill=Transition))+facet_wrap(~Zone)+
    geom_line(mapping=aes(x=DZoneD, y=mean, group=Transition, color=Transition), size=1.8)+
    scale_color_manual(values=c("black", "black", "black","black",
                                "black", "black", "black","black",
                                "black", "black", "black","black",
                                "black", "black", "black","black"))+
    geom_ribbon(mapping=aes(ymin=X2.50., ymax=X97.50., group=Transition), alpha=0.4)+
    scale_fill_manual(values=c("darkslategrey", "steelblue", "#E69F00", "#009E73",
                               "darkslategrey", "steelblue", "#E69F00", "#009E73",
                               "darkslategrey", "steelblue", "#E69F00", "#009E73",
                               "darkslategrey", "steelblue", "#E69F00", "#009E73"))+
    theme_classic(base_size=24) + theme(panel.border = element_blank(), panel.grid.major = element_blank(),legend.position="bottom",
                                        legend.key.size = unit(.25, 'in'),legend.title = element_text(size=14), legend.text = element_text(size=12),
                                        panel.grid.minor = element_blank(), axis.line = element_line(colour = "black"))+ 
    labs(y = "Transition Probability (Ψ)", x = "Housatonic River Discharge (m3/s)"))

print(Fig.psi.pred)

#Export plot
tiff("Fig.psi.pred", units="in", width=7, height=7, res=600)


DZoneD2 <- subset(DZoneD, sig == "y")

(Fig.psi.pred <- ggplot(DZoneD2, aes(x=DZoneD, y=mean, fill=Transition))+facet_wrap(~Zone)+
    geom_line(mapping=aes(x=DZoneD, y=mean, group=Transition, color=Transition), size=1.8)+
    scale_color_manual(values=c("black", "black", "black","black",
                                "black"))+
    geom_ribbon(mapping=aes(ymin=X2.50., ymax=X97.50., group=Transition), alpha=0.4)+
    scale_fill_manual(values=c("darkslategrey", "steelblue", "#E69F00","#009E73"))+
    theme_classic(base_size=24) + theme(panel.border = element_blank(), panel.grid.major = element_blank(),legend.position="bottom",
                                        legend.key.size = unit(.25, 'in'),legend.title = element_text(size=14), legend.text = element_text(size=12),
                                        panel.grid.minor = element_blank(), axis.line = element_line(colour = "black"))+ 
    labs(y = "Transition Probability (Ψ)", x = "Housatonic River Discharge (m3/s)"))



DZoneD3 <- subset(ms.mod, param == "Transition")
DZoneD3 <- subset(DZoneD3, hour <= 24)
DZoneD3$hour <- as.numeric(DZoneD3$hour)

ggplot(DZoneD3, aes(x=hour, y=mean, fill=Transition))+facet_wrap(~Zone)+  geom_col(alpha=0.65)+
  scale_fill_manual(values=c("darkslategrey", "steelblue", "#E69F00","#009E73"))+
  theme_classic(base_size=24) + theme(panel.border = element_blank(), panel.grid.major = element_blank(),legend.position="bottom",
                                      legend.key.size = unit(.25, 'in'),legend.title = element_text(size=14), legend.text = element_text(size=12),
                                      panel.grid.minor = element_blank(), axis.line = element_line(colour = "black"))+ 
  labs(y = "Transition Probability (Ψ)", x = "Hour (24 hr)")
    
    


