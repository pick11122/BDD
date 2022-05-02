# Charlie Wong
# CPTS 350: Symbolic Graph Project

from pyeda.inter import *


def get_even(num):
    even = []
    for i in range(0, num):
        if (i == 0 or i % 2) == 0:
            even.append(i)
    return even

def get_prime(num):
    primes = []
    for i in range(3, num):
        for j in range(2, int(i ** 0.5) + 1):
            if (i % j) == 0:
              break
        else:
            primes.append(i)
    return primes

def create_even_prime(evenSet, primeSet):
    """Creates  boolean formulas for even and prime sets"""
    # holds binary strings
    binEven = []
    binPrime = []
    # holds even, prime bool formulas
    eList = []
    pList = []

    # convert each even number to 5-bit unsigned binary 
    for num in evenSet:
        eBinary = "{0:05b}".format(num)
        binEven.append(eBinary)
    
    # convert each prime number to 5-bit unsigned binary 
    for num in primeSet:
        pBinary = "{0:05b}".format(num)
        binPrime.append(pBinary)
    
     # join binary to string type
    newString_e = ' '.join(str(e) for e in binEven)  
    newString_p = ' '.join(str(p) for p in binPrime) 
    
    
    # iterate over each binary string and characters (0,1)
    # append each seperate formula to eList 
    for i in binEven:
        element = i
        index = 0
        eFormula = ""
        for bit in element:
            if (bit == '0'):
                eFormula += f"~y[{index}] & "
            elif (bit == '1'):
                eFormula += f"y[{index}] & "
            index += 1
        eFormula = eFormula[:-3]   
        eList.append(eFormula)
    
    # iterate over each binary string and characters (0,1)
    # append each seperate formula to pList 
    for i in binPrime:
        element = i
        index = 0
        pFormula = ""
        for bit in element:
            if (bit == '0'):
                pFormula += f"~x[{index}] & "
            elif (bit == '1'):
                pFormula += f"x[{index}] & "
            index += 1
        pFormula = pFormula[:-3]   
        pList.append(pFormula)
    
    return eList, pList

def init_bdd():
    """ Creates initial BDD graph"""
    edgeList = []

    for i in range(0, 32):
        for j in range(0,32):
            if (i + 3) % 32 == j % 32 or (i + 8) % 32 == j % 32:
                formula = create_boolean_formula(i, j)
                edgeList.append(formula)
    
    R = connect_all(edgeList)
    RR = expr2bdd(R)            # Convert to bdd
    return RR
    

def create_boolean_formula(i, j):
    """ Creates boolean Formula from a pair of edges """
    index = 0
    xFormula = ""
    yFormula = ""
    # covert i,j to 5-bit unsigned binary 
    xBinary = "{0:05b}".format(i)
    yBinary = "{0:05b}".format(j)

    # iterate over the binary encoding of i to build x's boolean formula (xFormula)
    # append the string result to follow the boolean formula representation
    # i.e. 2 = 00010 => "~x[1] & ~x[2] & ~x[3] & [4] & ~x[5]"
    for bit in xBinary:
        if (bit == '0'):
            xFormula += f"~x[{index}] & "
        elif (bit == '1'):
            xFormula += f"x[{index}] & "
        index += 1
    
    index = 0
    # iterate over the binary encoding of j to build y's boolean formula (yFormula)
    for bit in yBinary:
        if (bit == '0'):
            yFormula += f"~y[{index}] & "
        elif (bit == '1'):
            yFormula += f"y[{index}] & "
        index += 1

    # remove extra '&'
    xFormula = xFormula[:-3]
    yFormula = yFormula[:-3]

    # encode pairs (x,y) into one boolean formula
    x_y_formula = f"{xFormula} & {yFormula}"
    return x_y_formula

def connect_all(edgeList):
    """ for each edge connect all boolean formulas with logic-OR and
        put into pyeda expression form"""
    
    joinedFormula = ""
    # add OR operator between each formula in the list
    for formula in edgeList:
        joinedFormula += f"{formula} | "
    
    joinedFormula = expr(joinedFormula[:-3])
    return joinedFormula

def compose_funct(r1,r2):
    """take 2 bdds return their composition"""

    # create boolean variables
    x = bddvars('x', 5)
    y = bddvars('y', 5)
    z = bddvars('z', 5)

    a = r1.compose({x[0]:z[0], x[1]:z[1], x[2]:z[2], x[3]:z[3], x[4]:z[4]})
    b = r2.compose({y[0]:z[0], y[1]:z[1], y[2]:z[2], y[3]:z[3], y[4]:z[4]})
    r = a & b
    return r.smoothing(z)

def compute_transitive_closure(RR2):
    """ compute RR2* using fixed point algorithim"""
    RR2star = RR2
    while True:
        H_prime = RR2star
        # H = H v (RR2 x H')
        RR2star = H_prime or compose_funct(H_prime, RR2)
        if RR2star.equivalent(H_prime):
            return RR2star

def statementA(RR2_star, EVEN, PRIME):
    """decide whether the statement "for each node u in {prime}, there is a node v in {even}
        such that you can reach v in a positive even number of steps"""
    
    # u,v nodes
    u = bddvars('x', 5)
    v = bddvars('y', 5)
    result = (~PRIME) | ((EVEN & RR2_star).smoothing(v))
    print (f"StatmentA: {result.equivalent(True)}")

def test_even_dbb(EVEN):
    y = bddvars('y', 5)
    t1 = EVEN.restrict({y[0]: 0, y[1]: 1, y[2]: 1, y[3]: 1, y[4]: 0}) # EVEN(14)
    t2 = EVEN.restrict({y[0]: 0, y[1]: 1, y[2]: 1, y[3]: 0, y[4]: 1}) # EVEN(13)
    return t1,t2

def test_prime_dbb(PRIME):
    x = bddvars('x', 5)
    t1 = PRIME.restrict({x[0]: 0, x[1]: 0, x[2]: 1, x[3]: 1, x[4]: 1}) # PRIME(7)
    t2 = PRIME.restrict({x[0]: 0, x[1]: 0, x[2]: 0, x[3]: 1, x[4]: 0}) # PRIME(0)
    return t1,t2

def test_RR_dbb(RR):
    x = bddvars('x', 5)
    y = bddvars('y', 5)
    t1 = RR.restrict({x[0]: 1, x[1]: 1, x[2]: 0, x[3]: 1, x[4]: 1, y[0]: 0, y[1]: 0, y[2]: 0, y[3]: 1, y[4]: 1}) # RR(27, 3)
    t2 = RR.restrict({x[0]: 1, x[1]: 0, x[2]: 0, x[3]: 0, x[4]: 0, y[0]: 1, y[1]: 0, y[2]: 1, y[3]: 0, y[4]: 0}) # RR(16,20)
    return t1, t2

def test_RR2_dbb(RR2):
    x = bddvars('x', 5)
    y = bddvars('y', 5)
    t1 = RR2.restrict({x[0]: 1, x[1]: 1, x[2]: 0, x[3]: 1, x[4]: 1, y[0]: 0, y[1]: 0, y[2]: 1, y[3]: 1, y[4]: 0}) # RR2(27, 6)
    t2 = RR2.restrict({x[0]: 1, x[1]: 1, x[2]: 0, x[3]: 1, x[4]: 1, y[0]: 0, y[1]: 1, y[2]: 0, y[3]: 0, y[4]: 1}) # RR2(27, 9)
    return t1, t2
    

if __name__ == "__main__":
    evenSet = []
    primeSet = []
    
    evenSet = get_even(32)
    primeSet = get_prime(32)
    evenSet, primeSet = create_even_prime(evenSet, primeSet)
    
    # join even, prime formulas on logic-OR
    e = connect_all(evenSet) 
    p = connect_all(primeSet)  

    # convert even,prime expressions to DBB    
    EVEN = expr2bdd(e)             
    PRIME = expr2bdd(p)
    print("done with {even} and {prime} sets")
   
    # DBB for R set
    RR = init_bdd() 
    a = bdd2expr(RR)
    b = expr2truthtable(a)
    print(b)
    print("done with R set")

    # compute BDD RR2 for the set RR (RR x RR)
    RR2 = compose_funct(RR,RR)
    print("done with RR2")
    # compute transitive closure RR2star of RR2
    RR2_star = compute_transitive_closure(RR2)            
    print("done with RR2star")
    statementA(RR2_star, EVEN, PRIME)

    # -----------------------------------------test cases----------------------------------
    print("")
    print("test cases")
    print("------------------")
    # test Even
    t_e1, t_e2 = test_even_dbb(EVEN)
    print(f"EVEN(14): {t_e1}")
    print(f"EVEN(13): {t_e2}")

     #test Prime
    t_p1, t_p2 = test_prime_dbb(PRIME)
    print(f"PRIME(7): {t_p1}")
    print(f"PRIME(2): {t_p2}")
    print("")

   # test R
    t_RR1, t_RR2 = test_RR_dbb(RR)
    print(f"RR(27,3):  {t_RR1}")
    print(f"RR(16,20): {t_RR2}")

    # test RR2
    t_RR2_1, t_RR2_2 = test_RR2_dbb(RR2)
    print(f"RR2(27,6): {t_RR2_1}")
    print(f"RR2(27,9): {t_RR2_2}")