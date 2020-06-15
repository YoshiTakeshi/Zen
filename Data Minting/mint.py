import math
import random
import pickle
import os.path
import matplotlib.pyplot as plt

import datetime

from sys import argv


Primes = [2]
Exponents = [0]
Anti_Factors = [0]

Anti_Prime = 1 # global variable
Anti_Prime_index = 0 # global variable

readfile = True
writefile = True

def Anti_Primes(index):
	global Anti_Prime_index
	global Anti_Prime

	if index == 0 :
		#print("Hello1")
		return 1
	elif Anti_Prime_index == index :
		#print("Hello2")
		return Anti_Prime
	elif Anti_Prime_index < index :
		#print("Hello3")
		M = 1
		while Anti_Prime_index < index :
			M = M*Primes[Anti_Factors[Anti_Prime_index+1]]
			Anti_Prime_index = Anti_Prime_index + 1
		Anti_Prime = Anti_Prime*M
		return Anti_Prime
	else :
		#print("Hello4")
		M = 1
		while Anti_Prime_index > index :
			M = M*Primes[Anti_Factors[Anti_Prime_index]]
			Anti_Prime_index = Anti_Prime_index - 1
		Anti_Prime = Anti_Prime//M
		return Anti_Prime

def generate_antiprimes_for(Number):
	global Anti_Prime
	global Primes
	global Exponents
	global Anti_Factors

	global readfile
	global writefile

	#print("Generate antiprime")

	Number_size = round(math.log(Number),0)

	#read_data

	if readfile and os.path.exists("data.zen") :
		print('Load data file...')
		with open("data.zen", "rb") as f:
			b = pickle.load(f)
			Primes = b[0]
			Exponents = b[1]
			Anti_Factors = b[2]
		readfile = False
		print('File Loaded...')

	while (Anti_Primes(len(Anti_Factors)-1)<2*Number):

		Min_x = float('inf')
		Min_j = 0

		time_start = datetime.datetime.now()

		for j in range(len(Primes)) :
			if Exponents[j-1]>Exponents[j] or j == 0:
				x = math.log(Primes[j])/math.log(1./(Exponents[j]+1.)+1.)
				if x<Min_x :
					Min_x = x
					Min_j = j

		Exponents[Min_j] = Exponents[Min_j] + 1

		if Min_j + 1 == len(Primes) :
			Exponents.append(0)
			Next_Prime = Primes[len(Primes)-1]+1
			j = 0

			while (Primes[j]*Primes[j]<=Next_Prime) :
				if Next_Prime%Primes[j] == 0:
					j=0
					Next_Prime = Next_Prime + 1
				else:
					j = j + 1

			Primes.append(Next_Prime)

		Anti_Factors.append(Min_j)


		time_end = datetime.datetime.now()
		delta = (time_end-time_start).total_seconds()
		seconds_left = (Number_size - round(math.log(Anti_Prime)))*delta

		print("{}/{} {}\r".format(round(math.log(Anti_Prime),0), Number_size, datetime.timedelta(seconds=seconds_left)), end="\r")


	#write data
	if writefile :
		with open("data.zen", "wb") as f:
			l = [Primes, Exponents, Anti_Factors]
			pickle.dump(l, f)
		writefile = False


def decentralize(Number) :

	generate_antiprimes_for(Number)
	#print("Decentralizing Number :",Number)

	i = len(Anti_Factors)-1
	Result = [[0,0]]

	while i > 0:

		if Anti_Primes(i) <= Number :
			Q = int(Number//Anti_Primes(i))
			Number = int(Number%Anti_Primes(i))

			Result.append((i,Q))

		while Number < Anti_Primes(i) and i>0:
			i = i - 1

		print(i,"               ", end="\r")
		#print("{}                                   \r".format(round(math.log(Number+1),0)),end="\r")

	if Number == 1 :
		Result.append((0,1))

	del Result[0]
	return Result

def centralize(Fact_Number) :
	Sum = 0

	for i in range(len(Fact_Number)) :
		#print(Anti_Primes(Fact_Number[i][0]))
		Sum = Sum + Anti_Primes(Fact_Number[i][0])*Fact_Number[i][1]

	#print("Centralizing Result :",Sum)

	return Sum


def string_decentralize(Message):
	Int_Code = int.from_bytes(Message,byteorder='big') #.encode()

	#Int_Code = int(Message.encode('hex'),16)

	Fact_Number = decentralize(Int_Code)
	Fact_Number.reverse()

	return Fact_Number

def string_centralize(Fact_Number):
	Expan_Number = centralize(Fact_Number)

	#print(Expan_Number)

	lenght = len(bin(Expan_Number)[2:])//8 + 1

	Code = Expan_Number.to_bytes(lenght, byteorder='big')

	Message = Code#.decode()

	return Message

def numerize(Fact_Number, EOF) :
	N = 1

	Minimize = minimize(Fact_Number)

	Result = [[0,0]]

	Max_XP = 0
	Max_YP = 0

	XP_Size = -1
	YP_Size = -2

	ZXP = 0
	ZYP = 0

	#print("Minimize : ", Minimize)

	for i in reversed(range(len(Minimize))):
		AP_Size = 1
		MP_Size = 1
		XP = 0
		YP = 0

		while Minimize[i][0] >= AP_Size :
			AP_Size = AP_Size*2
			XP = XP + 1

		while Minimize[i][1] >= MP_Size :
			MP_Size = MP_Size*2
			YP = YP + 1

		AP = Minimize[i][0]
		MP = Minimize[i][1]

		Result.append([MP,MP_Size])
		Result.append([YP,YP_Size])

		Result.append([AP,AP_Size])
		Result.append([XP,XP_Size])

		if Max_XP < XP :
			Max_XP = XP

		if Max_YP < YP :
			Max_YP = YP

		#print("[",XP,",", AP ,",",MP ,"]")

	XP_Size = 1
	YP_Size = 1

	while Max_XP >= XP_Size :
			XP_Size = XP_Size*2
			ZXP = ZXP + 1

	while Max_YP >= YP_Size :
			YP_Size = YP_Size*2
			ZYP = ZYP + 1

	for i in range(len(Result)):
		if Result[i][1] == -1 :
			Result[i][1] = XP_Size

		if Result[i][1] == -2 :
			Result[i][1] = YP_Size

	Result.append([ZYP,8])
	Result.append([ZXP,8])

	if EOF > 0 :
		Result.append([1,2])
	else :
		Result.append([0,2])

	del Result[0]

	return Result

def denumerize(Numerize) :
	EOF = Numerize[-1][0]

	ZXP = Numerize[-2][0]

	ZYP = Numerize[-3][0]

	Result = [[0,0]]

	i = len(Numerize)-4

	while i > 0 :


		XP = Numerize[i][0]
		AP = Numerize[i-1][0]
		YP = Numerize[i-2][0]
		MP = Numerize[i-3][0]

		i = i - 4

		Result.append([AP,MP])

	del Result[0]

	return deminimize(Result), EOF

def encode(Numerize) :
	Result = 0

	for i in range(len(Numerize)) :
		Result = Result*Numerize[i][1] + Numerize[i][0]

	return Result


def decode(Code):
	Result = [[0,0]]

	EOF = Code%2
	Code = Code//2

	Result.insert(0,[EOF,2])

	ZXP = Code%8
	Code = Code//8

	Result.insert(0,[ZXP,8])

	XP_Size = 2**ZXP

	ZYP = Code%8
	Code = Code//8

	Result.insert(0,[ZYP,8])

	YP_Size = 2**ZYP

	XP = Code%XP_Size
	Code = Code//XP_Size

	#print(ZXP, ZYP)

	Result.insert(0,[XP,XP_Size])

	AP_Size = 2**XP

	AP = Code%AP_Size
	Code = Code//AP_Size

	Result.insert(0,[AP,AP_Size])

	YP = Code%YP_Size
	Code = Code//YP_Size

	Result.insert(0,[YP,YP_Size])

	MP_Size = 2**YP

	MP = Code%MP_Size
	Code = Code//MP_Size

	Result.insert(0,[MP,MP_Size])

	while Code > 0 :
		XP = Code%XP_Size
		Code = Code//XP_Size

		Result.insert(0,[XP,XP_Size])

		AP_Size = 2**XP

		AP = Code%AP_Size
		Code = Code//AP_Size

		Result.insert(0,[AP,AP_Size])

		YP = Code%YP_Size
		Code = Code//YP_Size

		Result.insert(0,[YP,YP_Size])

		MP_Size = 2**YP

		MP = Code%MP_Size
		Code = Code//MP_Size

		Result.insert(0,[MP,MP_Size])

	del Result[-1]

	return Result

def minimize(Fact_Number):
	Result = [[0,0]]

	Result.append(Fact_Number[0])

	for i in range(1,len(Fact_Number)):
		Increment_1 = Fact_Number[i][0]-Fact_Number[i-1][0]
		Increment_2 = Fact_Number[i][1]-Fact_Number[i-1][1]

		Result_1 = 0
		Result_2 = 0

		if Increment_1 >= 0 :
			Result_1 = 2*Increment_1
		else :
			Result_1 = -2*Increment_1 + 1

		if Increment_2 >= 0 :
			Result_2 = 2*Increment_2
		else :
			Result_2 = -2*Increment_2 + 1

		Result.append([Result_1,Result_2])

	del Result[0]
	return Result

def deminimize(Fact_Number):
	Result = [[0,0]]

	Result.append(Fact_Number[0])
	for i in range(1,len(Fact_Number)):


		if Fact_Number[i][0]%2 == 0 :
			Increment_1 = Fact_Number[i][0]//2
		else:
			Increment_1 = -(Fact_Number[i][0]-1)//2

		Index_1 = Result[i][0]+Increment_1

		if Fact_Number[i][1]%2 == 0 :
			Increment_2 = Fact_Number[i][1]//2
		else:
			Increment_2 = -(Fact_Number[i][1]-1)//2

		Index_2 = Result[i][1]+Increment_2


		Result.append([Index_1,Index_2])

	del Result[0]
	return Result


def primesfrom2to(n):
    """ Input n>=6, Returns a array of primes, 2 <= p < n """
    sieve = np.ones(n//3 + (n%6==2), dtype=np.bool)
    for i in range(1,int(n**0.5)//3+1):
        if sieve[i]:
            k=3*i+1|1
            sieve[       k*k//3     ::2*k] = False
            sieve[k*(k-2*(i&1)+4)//3::2*k] = False
    return np.r_[2,3,((3*np.nonzero(sieve)[0][1:]+1)|1)]

def Save(Encode_Number, path) :
	lenght = len(bin(Encode_Number)[2:])//8 + 2
	out = open(path,"wb+")
	out.write(bytearray(Encode_Number.to_bytes(lenght, byteorder='big')))
	out.close()
	print('file '+ path + ' printed')

def Save_Bytes(Recieved_Message,path) :
	out = open(path,"wb+")
	out.write(Recieved_Message)
	out.close()
	print('file '+ path + ' printed')

def Read(path) :
	inp = open(path,"rb+")
	inp_code = int.from_bytes(inp.read(), byteorder='big')
	inp.close()
	return inp_code

def TSP(Fact_Number):
	print("Solving TSP")

	points = Fact_Number.copy()
	route = []

	route.append(points.pop(0))

	while len(points)>0 :
		print(len(points),'               ', end="\r")

		sights = []

		for j in range(len(points)):
			distance = (route[-1][0]-points[j][0])**2+(route[-1][1]-points[j][1])**2
			sights.append(1./(distance))

		probability = []

		sm = 0

		for j in range(len(sights)):
			sm = sm + sights[j]
			probability.append(sm)

		for j in range(len(probability)):
			probability[j] = probability[j]/probability[-1]

		p = random.random()

		for j in range(len(probability)):
			if p < probability[j] :
				route.append(points.pop(j))
				break

	return route


#------MINTING FILE--------
File_name = "mario.gif"

#Open File
f= open(File_name,"rb")
Send_Message = f.read() ##"Hello world"

#Decentralizing the file into a list (int, int)
Fact_Number = string_decentralize(Send_Message)
print("Fact_Numerize : ", Fact_Number)

#Solving the list of (int,int) as a Traveler-Salesman Problem,
#Finding the shortest route to travel all (int, int) point.
#And arrange the points (int, int) in that order of the optimal route
problem = TSP(Fact_Number)

#Plot the TSP solution
plt.plot(*zip(*problem))
plt.scatter(*zip(*Fact_Number))
plt.axis('scaled')
plt.show()

#Numerize and derive the coordnate list to vectors from start to finish as
#(+1,+1)->(+1,+3)->(-1, +1)...
#the positive change are even, the negative change are odd
Numerize_Number = numerize(problem,1)
print("Numerize : ", Numerize_Number)

#Encode the list into a single long integer
Encode_Number = encode(Numerize_Number)
print("Encode : ", Encode_Number)

#Save the intger into the file as binary
Save(Encode_Number, File_name + ".minted.out")


#------DEMINTING FILE--------
#Read the binary file
read = Read(File_name + ".minted.out")

#Decode it as a long integer
Decode_Number = decode(read)
print("Decode : ", Decode_Number)

#Extract the derivative list from the integerer and denumerize it,
#Restaure de décentralize List of the original message
Denumerize_Number, EOF = denumerize(Decode_Number)
print("Denumerize : ", Denumerize_Number)

#Restore the original file from the list
Recieved_Message = string_centralize(Denumerize_Number)

#Save the restored File
Save_Bytes(Recieved_Message, "deminted."+File_name)

#Print the file on console
#print("Assembled Message :",Recieved_Message.decode())
