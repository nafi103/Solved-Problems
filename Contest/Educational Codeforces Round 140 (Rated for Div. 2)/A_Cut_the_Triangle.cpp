for _ in range(int(input())):
    MooRsy = input()
    v = []
    u = []
    for _ in range(3):
        a ,b = [int(i) for i in input().split()]
        if a not in v:
            v.append(a)
        if b not in u:
            u.append(b)
    if len(v) == 3 or len(u) == 3:
        print("Yes")
    else:
        print("No")