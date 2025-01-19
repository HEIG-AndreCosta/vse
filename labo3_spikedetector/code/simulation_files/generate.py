with open("no_spike.txt", "w") as f:
    for i in range(10000):
        f.write(f"{i}\n")

with open("zeros.txt", "w") as f:
    for i in range(10000):
        f.write(f"0\n")
