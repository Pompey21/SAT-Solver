import matplotlib.pyplot as plt

# helper
ptive_inf = float('inf')
print('Positive Infinity: ',ptive_inf)

# data 
n = [i for i in range(4,16)]
times = [0,0,0.004906,0.006481,0.041227,0.163757,1.04096,18.0972,390.474,ptive_inf,ptive_inf,ptive_inf]


plt.plot(n, times)
plt.xlabel('N-pigeons')
plt.ylabel('Time (s)')
plt.show()