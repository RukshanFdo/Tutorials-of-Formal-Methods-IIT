MACHINE 
    PaperRound
    
VARIABLES 
    houseset
    
INVARIANT
    houseset <: NAT1
    
INITIALISATION
    houseset := {}
    
OPERATIONS
    
    add(new) =
    PRE new : NAT1 & new /: houseset
    THEN
        houseset := houseset \/ { new }
    END ;
    
    ans <-- number =
    BEGIN
        ans := card( houseset )
    END;
    
    numbHouses <-- getPapers(houseNumber)=
    PRE houseNumber : NAT1 & houseNumber : houseset
    THEN 
        numbHouses := 1
    END;
    
    cancelPapers(houseNumber)=
    PRE houseNumber : NAT1 & houseNumber : houseset
    THEN
        houseset := houseset - {houseNumber}
    END
    
END
