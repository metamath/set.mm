import sys

def tomm(pf):
    stk = []
    
    for step in reversed(pf):
        if step == 'a':
            stk.append('? ? ? ? ax-org')
        elif step == 'D':
            a = stk.pop()
            b = stk.pop()
            stk.append('? ? ? ' + b + ' ' + a + ' ax-ded')
        else:
            raise ValueError
    return stk[-1]

print tomm(sys.argv[1])
