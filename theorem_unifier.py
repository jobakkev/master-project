""" This program enumerates all possible combinations and orderings of quantifiers and fair allocation sections
    After listing them, equivalent expressions are unified and uninteresting expressions are filtered.
 """

import itertools
"""
theorems are expressed as three lists of five elements
the first list is an ordering of the five letters M,N,V,G,A
the second list consists of five choices between E and A representing the kind of negation (existential or universal)
the third list consists of five choices representing whether or not the quantifier is negated

we then iterate over the list of theorems. If a theorem is invalid, we discard it. If it is equivalent to a previously discovered theorem, we append it to that theorems class
"""
24*32*32

def list_all():
    """Generate a list of all possible theorems"""
    theorems = itertools.product(itertools.permutations(["M","G","N","V"]), itertools.product(["A","E"],repeat=4), itertools.product(range(2),repeat=5))
    return theorems

def merge_equivalence(classes, i, j):
    "Merges two equivalence classes into one"
    classes[i] = classes[i] + classes[j]
    del classes[j]

def equivalent(t1, t2):
    # Placeholder:
    eq = True
    i = 0
    inv = False #flags whether previous check found an inversion, in which case we allow the leading negator to be different
    while i <= 4:
        if i == 4:
            # the final parity must be equal unless the last check found an inversion
            if inv or (t1[2][i] == t2[2][i]):
                break
            else:
                return False
        if inv or (i==0) or (t1[2][i] == t2[2][i]):
            # we have either:
            #    same parity
            #    first type in statement, so we don't care for parity
            #    prev type was equiv under inversion, so parity was already checked (and must be different)
            inv = False # clear flag
            if t1[1][i] == t2[1][i]:
                # same quantifier
                if t1[0][i] == t2[0][i]:
                    # same type
                    # equiv under equality
                    # check next level
                    i+= 1
                    continue
                else:
                    # different type
                    # must be a swap
                    if  (t1[0][i] == t2[0][i+1]) and \
                        (t1[0][i+1] == t2[0][i]) and \
                        (t1[1][i] == t1[1][i+1] == t2[1][i+1]) and \
                        (t1[2][i+1] == t2[2][i+1] == 0):
                        # we have a swap
                        # this means we also checked the next type, quantifier and parity,
                        # so we can skip the next type
                        i += 2
                        continue
        else:
            # different parity, we must have inversion, or they are non-equivalent
            if (t1[0][i] == t2[0][i]) and \
               (t1[1][i] != t2[1][i]) and \
               (t1[2][i+1] != t2[2][i+1]):
                # same type, different quantifier, different parity before and after
                # we have equiv under inversion
                inv = True
                i += 1
                continue
        # all cases failed, so no equivalence
        return False
    return True

def filter_theorem(theorem):
    return False


if __name__ == "__main__":
    itr = list_all()
    # generate equivalence classes:
    class_index = 0
    count = 0
    skipped = 0
    merged = 0
    classes = dict()
    for theorem in itr:
        # pre-filter
        if(filter_theorem(theorem)):
            skipped += 1
            continue
        equiv = None
        to_merge = []
        # Verify if theorem is part of an earlier discovered class
        for eqclass, eqtheorems in classes.items():
            for eqtheorem in eqtheorems:
                if equivalent(theorem, eqtheorem):
                    # If the two theorems are equivalent
                    if equiv == None:
                        # and we have not found an earlier equivalence, remember this class
                        equiv = eqclass
                        break
                    else:
                        # and we have already discovered an earlier equivalence, 
                        # the two classes must be equivalent, and can be merged
                        to_merge.append(eqclass)
                        break
        for eqclass in to_merge:
            merged += 1
            merge_equivalence(classes, equiv, eqclass)
        if equiv != None:
            # Append the theorem to the class
            classes[equiv].append(theorem)
        else:
            # Create a new class for the theorem
            classes[class_index] = [theorem]
            class_index += 1
        count += 1
        if count % 1000 == 0:
            print(f"{count} theorems searched, {skipped} filtered. {len(classes)} equivalence classes, {merged} merged")
    print(len(classes.keys()))
