""" This program enumerates all possible combinations and orderings of quantifiers and fair allocation sections
    After listing them, equivalent expressions are unified and uninteresting expressions are filtered.
 """

import itertools
"""
theorems are expressed as two lists of five elements
the first list is an ordering of the five letters M,N,V,G,A
the second list consists of five choices between E and A representing the kind of quantification (existential or universal)

we then iterate over the list of theorems. If a theorem is invalid, we discard it. If it is equivalent to a previously discovered theorem, we append it to that theorems class
"""
24*32*32

def list_all():
    """Generate a list of all possible theorems"""
    theorems = itertools.product(itertools.permutations(["M","G","N","V"]), itertools.product(["∀","∃"],repeat=5))
    return theorems

def merge_equivalence(classes, i, j):
    "Merges two equivalence classes into one"
    classes[i] = classes[i] + classes[j]
    del classes[j]

def equivalent(t1, t2):
    # first check if ordering is same and quantifiers are inverted
    if t1[0]==t2[0]:
        # both have same variable order
        for i in range(5):
            if t1[1][i] == t2[1][i]:
                # quantifiers are not inverted, break
                break
            else:
                if i == 4:
                    return True
    i = 0
    while i <= 4:
        if i == 4:
            # the final quantifier must be equal
            if (t1[1][i] == t2[1][i]):
                break
            else:
                return False
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
                    (t1[1][i] == t1[1][i+1] == t2[1][i+1]):
                    # we have a swap
                    # this means we also checked the next type, quantifier and parity,
                    # so we can skip the next type
                    i += 2
                    continue
        # all cases failed, so no equivalence
        return False
    return True

def pre_filter(theorem):
    return False

forbidden_strings = [("G","M"), ("V", "N"), ("V", "M")]

def post_filter(theorem):
    # interleave quantifiers and types into a single string
    # ls =  theorem[0] + theorem[1]
    # ls[::2] = theorem[1]
    # ls[1::2] = theorem[0]
    ls = [theorem[1][i//2] if i%2 == 0 else theorem[0][i//2] for i in range(len(theorem[0])+len(theorem[1]))]
    ls.append('A')
    string = ''.join(ls)
    for forbidden in forbidden_strings:
        if forbidden[0] in string:
            if forbidden[1] in string[string.find(forbidden[0])+len(forbidden[0]):]:
                return True
    return False

def string_theorem(theorem):
    return ''.join([theorem[1][i//2] if i%2 == 0 else theorem[0][i//2] for i in range(len(theorem[0])+len(theorem[1]))])

def class_sort_key(cl):
    return min([len(''.join(char[0] for char in itertools.groupby(theorem[1]))) for theorem in cl])
    

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
        if(pre_filter(theorem)):
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
        if count % 100 == 0:
            print(f"{count} theorems searched, {skipped} filtered. {len(classes)} equivalence classes, {merged} merged")
    print(f"Classification done: {count} theorems searched, {skipped} filtered. {len(classes)} equivalence classes found, {merged} merged")
    to_filter = []
    post_filtered = 0
    filtered_classes = 0
    for eqclass, eqtheorems in classes.items():
        for index, theorem in enumerate(eqtheorems):
            if post_filter(theorem):
                to_filter.append((eqclass, index))
            else:
                post_filtered += 1
    for eqclass, theorem in reversed(to_filter): # need to do in reverse order to avoid indices changing after deletions
        del classes[eqclass][theorem]
        if len(classes[eqclass]) == 0:
            filtered_classes += 1
            del classes[eqclass]
    print(f"Filtering done: {len(to_filter)} theorems filtered, removing {filtered_classes} classes")
    print(f"Remaining classes: {len(classes)}, containing {post_filtered} theorems")
    # print classes
    for i, cl in enumerate(sorted(list(classes.values()),key=class_sort_key)):
        print(f"class {i}, {len(cl)} theorems: ")
        for theorem in cl:
            print(f"    {string_theorem(theorem)}")
