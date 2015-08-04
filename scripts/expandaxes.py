#!/usr/bin/env python

class Gensym:
    def __init__(self):
        self.count = 0

    def __call__(self):
        x = 'g%d' % self.count
        self.count += 1
        return x

gensym = Gensym()

def c(x,y):
    return '( %s -> %s )' % (x,y)

def n(x):
    return '-. %s' % (x,)

def A(x,y):
    return 'A. %s %s' % (x,y)

def k(x,y):
    return n(c(x,n(y)))

def e(x,y):
    #return k(c(x,y),c(y,x))
    return '( %s <-> %s )' % (x,y)

def el(x,y):
    return '%s e. %s' % (x,y)

def eq(x,y):
    z = gensym()

    return A(z,e(el(z,x),el(z,y)))

def dist(x,y):
    return n(A(x,eq(x,y)))

if __name__ == '__main__':
    x,y,z = 'x','y','z'
    ph = 'ph'

    print 'ax-9:', n(A(x,n(eq(x,y))))
    print
    print 'ax-9o', c(A(x,c(eq(x,y),A(x,ph))),ph)
    print
    print 'ax-10:', c(A(x,eq(x,y)),A(y,eq(y,x)))
    print
    print 'ax-10o', c(A(x,eq(x,y)),c(A(x,ph),A(y,ph)))
    print
    print 'ax-11:', c(eq(x,y),c(A(y,ph),A(x,c(eq(x,y),ph))))
    print
    print 'ax-15:', c(dist(z,x),c(dist(z,y),c(el(x,y),A(z,el(x,y)))))
    print
    print 'ax-two', n(A(x,eq(x,y)))
