content = "\n".join([str(i) for i in range(900)])

with open("linear.txt", "w") as f:
    f.write(content)

content = "0\n" * 900

with open("zeros.txt", "w") as f:
    f.write(content)

content = ("0\n" * 49 + "1000\n" + "0\n" * 100) * 17

with open("constant_spikes_16_windows.txt", "w") as f:
    f.write(content)
