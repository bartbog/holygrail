def extension1(cnf_clauses, F_prime):
    """
    
        Add all clauses that are true based on the assignment by the model of Fprime
        :param cnf_clauses: a collection of clauses (list of literals).
        :param F_prime: hitting set : a list of clauses.
        
        :type cnf_clauses: iterable(iterable(int))
        :type F_prime: iterable(int)    
        
    """
    # new set of validated literals
    new_F_prime = set(F_prime)
    
    # all literals (clauses with 1 element) validated in current hitting set
    validated_literals = {cnf_clauses[index][0] for index in new_F_prime if len(cnf_clauses[index]) == 1}
    
    # remaining clauses to check for validation
    remaining_clauses = {i for i in range(len(cnf_clauses))} - F_prime
    
    for c in remaining_clauses:
        clause = cnf_clauses[c]
        for literal in validated_literals:
            if literal in clause:
                new_F_prime.add(c)

    #validated_variables = flatten_set(validated_clauses)
    return new_F_prime



def extension2(cnf_clauses, F_prime, random_assignment = True):
    """
    
            Step 1 : Compute clauses with unique literals
            
            Step 2 :
                2.1 Compute validated clauses
                2.2 Compute remaining clauses
            
            Step 3:
                3.1 Compute all literal in validated clauses
                3.2 remove already validated literals from unique literal clauses
                3.3 remove negation of already validated literals from unique clauses
            
            Step 4:
                4.1 Seperate all remaining literals in validated clauses in 2 parts:
                    4.1.1 literals without negation of literal present
                    4.1.2. literals with negation present
            
            Step 5: Add all remaining clauses validated by assignement literals w/o negation
            
            Step 6:
                6.1a choose first literal from all literals with negation
                                or
                6.1b choose literal with best clause propagation
                6.2 Add all remaining clauses validated by assignement of literal                 
                
    """
    
    new_F_prime = set(F_prime)

    # Step 1 : clauses with unique literals
    # clauses with 1 literal 
    unique_literal_validated_clauses = {index for index in new_F_prime if len(cnf_clauses[index]) == 1}
    
    # literals validated in clauses with 1 literal
    validated_literals = {cnf_clauses[index][0] for index in unique_literal_validated_clauses}
    
    # non-unique clauses
    remaining_clauses = {i for i in range(len(cnf_clauses))} - unique_literal_validated_clauses
    
    # Step 2 : clauses with unique literals
    # all clauses satisfied by current single literal assignments of Fprime
    satisfied_clauses = set()
    
    # for every literal in validated literal check for any clause satisfied 
    for literal in validated_literals:
        for c in remaining_clauses:
            clause = cnf_clauses[c]
            if literal in clause:
                satisfied_clauses.add(c)
                new_F_prime.add(c)
    
    # remove unique literal clauses already validated
    satisfied_clauses -= unique_literal_validated_clauses

    remaining_clauses -= satisfied_clauses
    
    # remaining validated clauses in F prime
    assert all([True if -i not in validated_literals else False for i in validated_literals]), "literal conflict"
        
    # remaining literals to assign
    other_literals = flatten_set([cnf_clauses[index] for index in satisfied_clauses])

    # remove already validated literals
    other_literals -= validated_literals
    
    # remove negated already validated literals
    other_literals -= {-i for i in validated_literals}
    
    # filtered literals with negated literal also present 
    conflict_free_literals = {i for i in other_literals if -i not in other_literals}
    
    # remove all clauses validated by conflict free literals
    for literal in conflict_free_literals:
        clauses_to_remove = set()
        for c in remaining_clauses:
            clause = cnf_clauses[c]
            if literal in clause:
                clauses_to_remove.add(c)
                new_F_prime.add(c)
        remaining_clauses -= clauses_to_remove

    validated_literals |= conflict_free_literals

    other_literals -= conflict_free_literals
    # remaining conflictual literals to validate
    conflictual_literals = set(other_literals)    
   
    # check if only conflictual literals are present in conflictual literals
    assert all([True if -i in conflictual_literals else False for i in conflictual_literals]), "conflictual literals error"
    assert len(conflictual_literals) % 2 == 0, "check remaining literals are present in pairs"
    
    # for every literal, remove its negation and 
    while len(conflictual_literals) > 0:
        # randomly assigns truthness value
        if random_assignment:
            literal = conflictual_literals[0]
        else: 
            literal = find_best_literal(cnf_clauses, remaining_clauses, conflictual_literals)
            
        # SANITY CHECK : add to validated literals
        assert literal not in validated_literals, "literal already present"
        assert -literal not in validated_literals, "negation of literal already present, conflict !!!"
        validated_literals.add(literal)

        # remove literal and its negation
        conflictual_literals.remove(literal)
        conflictual_literals.remove(-literal)

        # remove validated clauses
        clauses_to_remove = set()
        
        for c in remaining_clauses:
            clause = cnf_clauses[c]
            if literal in clause:
                clauses_to_remove.add(c)
                new_F_prime.add(c)
        remaining_clauses -= clauses_to_remove
    # print("validated literals:", validated_literals)   
    return new_F_prime



def extension2silly(cnf_clauses, F_prime, random_assignment = True):
    """
    0.0
            Repeatedly apply extension 2 until there is no more progress
            Propagate as much as possible
                
    """
    # TODO: 
    # - add while loop to propagate as long as possible as long as possible
    #   whenever len(other_literals ) > 0 
    # 
    # - exploit validatable clauses
    
    clauses_added = True
    new_F_prime = set(F_prime)

    while(clauses_added):
        ext2_F_prime = extension2(cnf_clauses, new_F_prime, random_assignment)
        ppprint({"new_F_prime" : new_F_prime,
                 "ext2_F_prime":ext2_F_prime,
                 "cnf_clauses": cnf_clauses
                  })
        clauses_added = ext2_F_prime > new_F_prime
        new_F_prime = set(ext2_F_prime)
        
    return new_F_prime


def extension3(cnf_clauses, F_prime, random_assignment = True):

    """
    
        Greedy Approach : 
            validated literals = {}

            1. Fprime = {unique literal clauses in F_prime} + {other validated clauses in F_prime} (sanity check)
                . seperate the unique literal clauses from other clauses in Fprime
                    => unique clause literals (a) => add to validated literals

            2. {clauses validated but not in F_prime} = {validated clauses using unique literal clauses in F_prime} - {F_prime}
                . get clauses that are validated by unique literals in Fprime but are not present in Fprime
                    => get the literals
                    => remove the unique literals 
                    => literals from validated clauses but not in F_prime and not a unique clause literal (b)

            3. {validated clauses in F_prime that have no literals from unique literal clauses}:
                . seperate into 
                    - conflict free literals : 
                        => 
                    - conflictual literals :
                        . this is a hitting set problem solve with optimal hitting set with special case of negated literals also present? 
                        . get a number of literals that covers the clauses 
                    => literals from F_prime that need to be  (c)

            4. {validated clauses in F_prime with literals from unique literal clauses} -  {unique literal clauses in F_prime}
                . {get the literals} - {validated literals up until now} - {negation of validated literals up until now}
            
    """

    new_F_prime = set(F_prime)
    
    all_clauses = {i for i in range(len(cnf_clauses))}
    
    # Step 1 : clauses with unique literals
    # clauses with 1 literal 
    unique_literal_validated_clauses = {index for index in new_F_prime if len(cnf_clauses[index]) == 1}
    unique_literals = getLiteralsSubsetClauses(cnf_clauses, unique_literal_validated_clauses) 

    # all clauses validated by current unique literal assignments
    all_validated_clauses = getClausesValidatedByLiterals(cnf_clauses, all_clauses, unique_literals)
    
    # all remaining validated clauses by F_prime assignement not in unique literal assignement
    remaining_validated_clauses = (new_F_prime | all_validated_clauses) - unique_literal_validated_clauses

    remaining_literals_validated_clauses = getLiteralsSubsetClauses(cnf_clauses, remaining_validated_clauses)

    remaining_literals_f_prime = getLiteralsSubsetClauses(cnf_clauses, F_prime)

    remaining_literals_validated_clauses -= unique_literals

    
    # remaining propagatable clauses
    remaining_clauses = all_clauses
    remaining_clauses -= new_F_prime
    remaining_clauses -= all_validated_clauses
    remaining_clauses -= unique_literal_validated_clauses
    
    
    # ppprint({
    #     "cnf_clauses": cnf_clauses, 
    #     "F_prime" : F_prime, 
    #     "unique_literals":unique_literals, 
    #     "all_validated_clauses": all_validated_clauses, 
    #     "remaining_literals_validated_clauses": remaining_literals_validated_clauses,
    #     "remaining_clauses":remaining_clauses
    # })
    
    return new_F_prime