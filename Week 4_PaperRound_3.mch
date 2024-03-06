MACHINE  PaperRound_3

  SETS
    ANSWER = { yes, no } ;

    OUTCOME = { NoMoreDeliveries, NotDeliveredTo, NotDeliveringPaperAndMagazine } ;

    STATUS = { PaperAndMagazine, OnlyPaper, OnlyMagazine, NoDeliveries, NotBothPaperAndMagazine }
               

  CONSTANTS
      MAX_DELIVERIES                         /* Exercise 3.7 */
     
  PROPERTIES
      MAX_DELIVERIES : NAT1  &  MAX_DELIVERIES = 10


  VARIABLES 
    houseset,
    magazineHouses                          /* Exercise 3.3 */

  INVARIANT 
    houseset <: NAT1 
    &
    card( houseset ) <= MAX_DELIVERIES   /* Exercise 3.7 */
    &
    magazineHouses <: NAT1 
    &
    magazineHouses <: houseset     
   
  
  INITIALISATION 
       houseset := {}  
    ||
       magazineHouses := {}



  OPERATIONS

    addNewHouse( newHouse ) =
      PRE
           newHouse : NAT1  &  newHouse /: houseset & 
           card( houseset ) < MAX_DELIVERIES            /* Exercise 3.7 */
      THEN 
           houseset := houseset \/ { newHouse }
      END
      ;

    numbHouses <-- howManyHouses =
        BEGIN
            numbHouses := card( houseset )
        END ;           

    ans <-- getsPapers( houseNumber ) =
              PRE
                     houseNumber : NAT1 & houseNumber : houseset
              THEN
                     ans := 1    
              END
              ; 


    //  Using PRE-condition to avoid  min( {} )  error
    housenumb <-- firsthouse_v1 =
                    PRE
                          houseset /= {} 
                    THEN
                          housenumb := min( houseset )
                    END
                    ;
                  
                  
    //  Using IF & returning a very large number to avoid  min( {} )  error
    housenumb <-- firsthouse_v2 =
                  BEGIN
                         IF ( card(houseset) /= 0 )
                         THEN
                               housenumb := min( houseset )
                         ELSE
                               housenumb := 99999999999       
                         END
                  END
                  ;

    
                
    housenumb <-- lasthouse =
                  BEGIN
                        IF ( houseset /= {} )
                        THEN
                              housenumb := max( houseset )
                        ELSE
                              housenumb := 0
                        END
                  END
                  ;
    
    answer <-- haspaper( housenumb ) = 
               PRE
                    housenumb : NAT1
               THEN
                     IF ( housenumb : houseset )
                     THEN
                           answer := yes
                     ELSE
                           answer := no
                     END
               END
               ;


    outcome <-- stopdelivery( housenumb ) = 
                PRE
                     housenumb : NAT1
                THEN
                     IF ( housenumb : houseset )
                     THEN
                             houseset := houseset - { housenumb }
                           ||
                             outcome := NoMoreDeliveries 
                     ELSE
                           outcome := NotDeliveredTo
                     END
                END
                ;

    deliverMagazine( housenumb ) = 
      PRE
           housenumb : NAT1  &  housenumb /: magazineHouses &
           housenumb : houseset                                   /* Exercise 3.7 */
      THEN 
           magazineHouses := magazineHouses \/ { housenumb }
      END
      ;
 
    stopMagazine( housenumb ) = 
      PRE
           housenumb : NAT1
      THEN
            magazineHouses := magazineHouses - { housenumb }
      END
      ;

    status <-- deliveries( housenumb ) = 
      PRE
           status : STATUS  &  housenumb : NAT1
      THEN
            IF  housenumb : houseset  &  housenumb : magazineHouses
            THEN
                  status := PaperAndMagazine  

            ELSIF( housenumb : houseset )  
            THEN   
                  status := OnlyPaper  

            ELSIF( housenumb : magazineHouses )  
            THEN  
                  status := OnlyMagazine
            ELSE
                  status := NoDeliveries
            END
       END
       ;



    outcome <-- stopalldeliverys( housenumb ) = 
                PRE
                     outcome : OUTCOME  &  housenumb : NAT1
                THEN
                     IF ( ( housenumb : houseset ) & ( housenumb : magazineHouses) )
                     THEN
                             houseset := houseset - { housenumb }
                          ||
                             magazineHouses := magazineHouses - { housenumb }
                          ||
                             outcome := NoMoreDeliveries 
                     ELSE
                           outcome := NotDeliveringPaperAndMagazine  
                     END
                END
                ;

/*  Exercise 3.7 */

   moreDeliveries <-- howManyMore =
            BEGIN
                   moreDeliveries :=   MAX_DELIVERIES - card( houseset ) 
            END


END 

