from itertools import product

# Define the CNF condition as a function used as input to CNFReducer
def check_cnf(a, b, c, d, e, f, g, h, i, j):
    return ((c or f or h) and
    (h or g or f) and
    (a or not e or g) and
    (b or d or j) and
    (c or a or i) and
    (not c or a or f) and
    (b or j or h) and
    (g or f or not a) and
    (i or h or f) and
    (g or i or a) and
    (a or not e or f) and
    (b or e or g) and
    (b or i or h) and
    (not j or e or f) and
    (c or h or e) and
    (c or b or not a) and
    (a or i or h) and
    (b or i or a) and
    (h or not c or i) and
    (c or g or j))

# Generated reduced CNF by CNFReducer
def check_reduced_cnf(a, b, c, d, e, f, g, h, i, j):
    return (((not a and g) or (not a and j) or (b and g) or (b and j) or (c)) and
    ((not e and not a and h and i) or (not e and f and i) or (a and f) or (g)) and
    ((b) or (d and e and h) or (d and g and h) or (e and j) or (g and j)) and
    ((not j and not e and not c) or (not j and a) or (a and e) or (f)) and
    ((not c and a and b and e and f) or (c and i) or (e and f and i) or (h)) and
    ((a) or (b and c) or (i)))
    
# Iterate over all 5-bit patterns (2^5 combinations)
print("Checking all 32 truth assignments:")
matched = 0
unmatched = 0
for bits in product([False, True], repeat=10):
    a, b, c, d, e, f, g, h, i, j = bits  # Unpack binary values to variables
    result = check_cnf(a, b, c, d, e, f, g, h, i, j)
    result2 = check_reduced_cnf(a, b, c, d, e, f, g, h, i, j)
    if result == result2:
        matched += 1
    else:
        unmatched += 1
    
    print(f"a={a}, b={b}, c={c}, d={d}, e={e}, f={f}, g={g}, h={h}, i={i}, j={j} -> input {result} output {result2} compare {result == result2} ")
print("result matched", matched, "unmatched", unmatched)
