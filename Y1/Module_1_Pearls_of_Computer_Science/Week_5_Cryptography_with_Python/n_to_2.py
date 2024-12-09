number = int(input("Number to be factored: "))
num_rep = []
while number > 0:
    num_rep.append(number % 2)
    number //= 2

print(list(reversed(num_rep)))
