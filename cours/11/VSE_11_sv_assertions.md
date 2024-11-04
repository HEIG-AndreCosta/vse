# 23

![alt text](image-4.png)
OK OK

# 24

![alt text](image-5.png)
OK NOK

# 26

![alt text](image-6.png)
OK OK

## 27

![](image.png)

OK NOK

## 28

![](image-1.png)

OK OK

## 29

![alt text](image-2.png)

OK OK

## 30

![alt text](image-3.png)

OK OK

## Exemple 1

- Lorsqu’une requête (activation de req) est émise, alors un acknowledge (activation de ack) doit arriver au plus tard 5 cycles d’horloge après

```systemverilog
req |-> ##[0:5] ack;
```

## Exemple 2

- Les entrées a et b doivent rester stables tant que valid est actif

```systemverilog
valid |-> $stable(a) && $stable(b); // Pas bon, car si a suit valid, a sera rising et pas stable 

valid && $stable(valid) |-> $stable(a) && $stable(b); // Ok pour des pulses plus grandes que 1 cycle

valid[*2] |-> $stable(a) && $stable(b); // Ok, on attend qu'il soit stable (2 cycles)
```
