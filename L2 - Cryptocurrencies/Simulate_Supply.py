import math
import random
from scipy.stats import norm
import matplotlib.pyplot as plt

def simulate(metal,block_time,period):
    History = []
    Raw_Reward = 2520
    Supply = 0
    Ratio = (metal+math.pow(metal*metal+4,0.5))/2.

    for i in range(int(Period*60/block_time)):

        V = math.pow(Ratio,norm.ppf(random.random(),0,1))#qrng.get_double(),0,1)) for Quantum Random Number Generator
        Supply = Supply + Raw_Reward*V

        for j in range(int(block_time*2)):
            History.append(Supply)

        Raw_Reward = 2520*math.pow(0.5,(math.log(i+1))/math.log(Ratio))

        print "({}, {}, {}) {}/{}\r".format(metal,block_time,period,i+1,int(Period*60/block_time)),

    print "({}, {}, {}) {}/{} Done\r".format(metal,block_time,period,i+1,int(Period*60/block_time))

    return History

#Period in hours
Period = 365*24 

Golden_Yen = simulate(1,15,Period)
Silver_Ken = simulate(2,5,Period)
Bronze_Jen = simulate(3,2.5,Period)
#Fiat_Dollar = simulate(607,60*24,Period)

plt.plot(Golden_Yen,'y')
plt.plot(Silver_Ken,'b')
plt.plot(Bronze_Jen,'r')
#plt.plot(Fiat_Dollar,'g')

print "Golden Yen Supply : {}".format(Golden_Yen[-1])
print "Silver Ken Supply : {}".format(Silver_Ken[-1])
print "Bronze Jen Supply : {}".format(Bronze_Jen[-1])
#print "Fiat Dollar Supply : {}".format(Fiat_Dollar[-1])

print "KEN/YEN : {}".format(Silver_Ken[-1]/Golden_Yen[-1])
print "JEN/KEN : {}".format(Bronze_Jen[-1]/Silver_Ken[-1])
print "JEN/YEN : {}".format(Bronze_Jen[-1]/Golden_Yen[-1])
#print "YEN/USD : {}".format(Fiat_Dollar[-1]/Golden_Yen[-1])

#plt.yscale('log')
plt.show()
