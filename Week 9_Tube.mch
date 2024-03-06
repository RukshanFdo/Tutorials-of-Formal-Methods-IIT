MACHINE 
    Tube
       
  SETS
      
    LINE = { Bakerloo, Victoria, Northern, Circle } ;

    STATION = { 
             
                Baker_Street, Regents_Park, Oxford_Circus, Piccadilly_Circus, Charing_Cross,
                
                Great_Portland_Street, Euston_Square,
               
                Warren_Street,  
               
                Goodge_Street, Tottenham_Court_Road, Leicester_Square,
                
                UnknownStation
              } ;             
    
    JOURNEY_STATUS = { Journey_is_Empty, 
                       Journey_is_MaxLength, 
                       Journey_Only_Has_Start_station, 
                       Journey_Can_Be_Extended 
                     } ;

    //  Exercise 7.9

    REPORT = { ERROR_Journey_is_MaxLength,
               Start_Station_Removed_From_Journey, 
               ERROR_Journey_Empty,  
               
               //  Exercise 7.9
               First_Station_Added_To_Journey,
               Adjacent_Station_Added_To_Journey, 
               ERROR_NonAdjacent_Station_NOT_Added_To_Journey,        
               ERROR_UNKNOWN
               
               
             } ;
         
             
    JOURNEY_REPORT = { Journey_Remaining,            // Exercise 7.8 (f)
                       Journey_Completed,
                       ERROR_Journey_Not_That_Long
                     } 
   
    
   CONSTANTS
      MaxJourneyLength, JOURNEY, UNDEFINED_JOURNEY,
      
      onLine,                 // Exercise 7.5
    
      Bakerloo_NtoS,          // Exercise 7.6
      Victoria_NtoS,
      Northern_NtoS,
      Circle_WtoE,
    
      Bakerloo_adjacent_NtoS,  Bakerloo_adjacent_StoN,  Bakerloo_adjacent,      // Exercise 7.7
      Victoria_adjacent_NtoS,  Victoria_adjacent_StoN,  Victoria_adjacent,
      Northern_adjacent_NtoS,  Northern_adjacent_StoN,  Northern_adjacent,
      Circle_adjacent_WtoE,    Circle_adjacent_EtoW,    Circle_adjacent,
      Tube_adjacent,
      
      NO_JOURNEY_LEFT          // Exercise 7.8 (f)
      
   
   
   PROPERTIES
      MaxJourneyLength : NAT1  &  MaxJourneyLength = 7  
      &
      JOURNEY = iseq(STATION)    
      &
      UNDEFINED_JOURNEY : JOURNEY  &  UNDEFINED_JOURNEY = []            
              
      &
      // Exercise 7.5
      onLine  :  STATION <-> LINE               
      &
      UnknownStation /: dom( onLine )
      & 
      onLine =     ( { Baker_Street, Regents_Park, Oxford_Circus, Piccadilly_Circus, Charing_Cross } * { Bakerloo } )
                \/
                   ( { Baker_Street, Great_Portland_Street, Euston_Square } * { Circle } )
                \/
                   ( { Warren_Street, Oxford_Circus } * { Victoria } )
                \/                  
                   ( { Warren_Street, Goodge_Street, Tottenham_Court_Road, Leicester_Square, Charing_Cross } * { Northern } )  
     
     
      // Exercise 7.6
      &
      Bakerloo_NtoS : iseq( STATION ) 
      &
      Bakerloo_NtoS = [ Baker_Street, Regents_Park, Oxford_Circus, Piccadilly_Circus, Charing_Cross ]

      &
      Victoria_NtoS : iseq( STATION ) 
      &
      Victoria_NtoS = [ Warren_Street, Oxford_Circus ]
      
      &
      Northern_NtoS : iseq( STATION ) 
      &
      Northern_NtoS = [ Warren_Street, Goodge_Street, Tottenham_Court_Road, Leicester_Square, Charing_Cross ]
      
      &
      Circle_WtoE   : iseq( STATION ) 
      &
      Circle_WtoE   = [ Baker_Street, Great_Portland_Street, Euston_Square ]


      // Exercise 7.7
      &
      Bakerloo_adjacent_NtoS : STATION <-> STATION
      &
      Bakerloo_adjacent_NtoS = { Baker_Street |-> Regents_Park,       Regents_Park |-> Oxford_Circus, 
                                 Oxford_Circus |-> Piccadilly_Circus, Piccadilly_Circus |-> Charing_Cross }
      &
      Bakerloo_adjacent_StoN : STATION <-> STATION
      &
      Bakerloo_adjacent_StoN = Bakerloo_adjacent_NtoS~ 
      &
      Bakerloo_adjacent : STATION <-> STATION
      &
      Bakerloo_adjacent =  Bakerloo_adjacent_NtoS \/ Bakerloo_adjacent_StoN 
      

      &
      Victoria_adjacent_NtoS : STATION <-> STATION
      &
      Victoria_adjacent_NtoS = { Warren_Street |-> Oxford_Circus }
      &
      Victoria_adjacent_StoN : STATION <-> STATION
      &
      Victoria_adjacent_StoN = Victoria_adjacent_NtoS~ 
      &
      Victoria_adjacent : STATION <-> STATION
      &
      Victoria_adjacent =  Victoria_adjacent_NtoS \/ Victoria_adjacent_StoN


      &
      Northern_adjacent_NtoS : STATION <-> STATION
      &
      Northern_adjacent_NtoS = { Warren_Street |-> Goodge_Street,           Goodge_Street |-> Tottenham_Court_Road, 
                                 Tottenham_Court_Road |-> Leicester_Square, Leicester_Square |-> Charing_Cross     }
      &
      Northern_adjacent_StoN : STATION <-> STATION
      &
      Northern_adjacent_StoN = Northern_adjacent_NtoS~ 
      &
      Northern_adjacent : STATION <-> STATION
      &
      Northern_adjacent =  Northern_adjacent_NtoS \/ Northern_adjacent_StoN 


      &
      Circle_adjacent_WtoE : STATION <-> STATION
      &
      Circle_adjacent_WtoE = { Baker_Street |-> Great_Portland_Street,  Great_Portland_Street |-> Euston_Square }
      &
      Circle_adjacent_EtoW : STATION <-> STATION
      &
      Circle_adjacent_EtoW = Circle_adjacent_WtoE~ 
      &
      Circle_adjacent : STATION <-> STATION
      &
      Circle_adjacent =  Circle_adjacent_WtoE \/ Circle_adjacent_EtoW

    
      &
      Tube_adjacent : STATION <-> STATION
      &
      Tube_adjacent = Bakerloo_adjacent \/ Victoria_adjacent \/ Northern_adjacent \/ Circle_adjacent
      
      &
      NO_JOURNEY_LEFT : JOURNEY  &  NO_JOURNEY_LEFT = []         // Exercise 7.8 (f)
      
      
  DEFINITIONS
      
      // Exercise 7.9
      adjacentStation( s1, s2 ) == ( s1 : STATION & s2 : STATION &  ( s1 |-> s2 ) : Tube_adjacent ) 
      
    
  VARIABLES
      tube_journey

  INVARIANT
      tube_journey : JOURNEY  &  size( tube_journey ) <= MaxJourneyLength
      &
      UnknownStation /: ran( tube_journey )
    
  INITIALISATION
      tube_journey := UNDEFINED_JOURNEY
       
       
   
   OPERATIONS
       
    report <-- AddNextStationToJourney( station ) =
        PRE 
            station :  STATION             &  
            station /: ran( tube_journey ) &     
            station /= UnknownStation      &
            report  :  REPORT               
        THEN 
            
            IF   ( size( tube_journey ) = MaxJourneyLength )                  
            THEN
                  report := ERROR_Journey_is_MaxLength
                   
            ELSIF ( tube_journey = UNDEFINED_JOURNEY )                        
            THEN                                                              
                  tube_journey  := tube_journey <- station  ||
                  report := First_Station_Added_To_Journey
                
            ELSIF  ( size( tube_journey )  < MaxJourneyLength  &              
                     adjacentStation( last( tube_journey ), station ) )       
            THEN
                  tube_journey  := tube_journey <- station  ||
                  report := Adjacent_Station_Added_To_Journey
                
            ELSIF  ( size( tube_journey )  < MaxJourneyLength  &              
                     not( adjacentStation( last( tube_journey ), station ) )  
                   )                                                          
            THEN
                  report := ERROR_NonAdjacent_Station_NOT_Added_To_Journey
                
            ELSE
                 report := ERROR_UNKNOWN
            END 
        END 
        ;


    report <-- RemoveStartStationFromJourney = 
              PRE 
                    report : REPORT
              THEN 
                      // skip 

                      IF ( tube_journey /= UNDEFINED_JOURNEY )                  // Exercise 7.4
                      THEN                                                      
                            tube_journey  := tail( tube_journey )         ||    
                            report := Start_Station_Removed_From_Journey        
                      ELSE                                                      
                            report := ERROR_Journey_Empty                       
                      END                                                       

              END 
              ;


    status <-- JourneyStatus =
        PRE 
            status : JOURNEY_STATUS    
        THEN 
            IF  ( tube_journey = UNDEFINED_JOURNEY )
            THEN
                 status := Journey_is_Empty 
            ELSIF 
                 ( size(tube_journey) = MaxJourneyLength ) 
            THEN
                 status := Journey_is_MaxLength
            ELSIF
                 ( size(tube_journey) = 1 ) 
            THEN
                 status := Journey_Only_Has_Start_station                  
             ELSE
                 status := Journey_Can_Be_Extended
            END 
        END 
        ;
        

     //  Exercise 7.8 (a) 

     jlength <-- journeyLength = 
                    
 		            BEGIN
                          jlength := size( tube_journey )  
                    END
                    ;
                      
     //  Exercise 7.8 (b) 

     journey <-- returnJourney = 
                    
		            BEGIN
                          journey := rev( tube_journey )  
                    END
                    ;
                      
     
     //  Exercise 7.8 (c) 

     firststation <-- firstStation = 
                    PRE 
                         firststation : STATION    
                    THEN 
                          IF  ( tube_journey = UNDEFINED_JOURNEY ) 
                          THEN
                                firststation := UnknownStation
                          ELSE
                                firststation := first( tube_journey )  
                          END
                            
                    END
                    ;
                      
                      
     //  Exercise 7.8 (d) 
     laststation <-- lastStation = 
                    PRE 
                         laststation : STATION    
                    THEN 
                          IF  ( tube_journey = UNDEFINED_JOURNEY ) 
                          THEN
                                laststation := UnknownStation
                          ELSE
                                laststation := last( tube_journey )  
                          END
                            
                    END
                    ;
                      

     //  Exercise 7.8 (e) 

     lines <-- goOnLines = 
                    PRE 
                         lines <: LINE    
                    THEN 
                          IF  ( tube_journey = UNDEFINED_JOURNEY ) 
                          THEN
                                lines := {}
                          ELSE
                                lines :=  onLine[ ran( tube_journey ) ] 
                          END
                            
                    END
                    ;
                      

     //  Exercise 7.8 (f) 
     
     report, journey <-- journeyLeft( numbStationsDone ) = 
                    PRE 
                         report : JOURNEY_REPORT &
                         
                         numbStationsDone : NAT 
                         
                    THEN 
                          IF  ( numbStationsDone = size(tube_journey) ) 
                          THEN
                                 journey :=  NO_JOURNEY_LEFT   ||
                                 report      :=  Journey_Completed
                                 
                          ELSIF  ( numbStationsDone < size(tube_journey) ) 
                          THEN    
                                 journey :=  ( tube_journey \|/ numbStationsDone ) ||
                                 report      :=  Journey_Remaining  
                                
                          ELSIF  ( numbStationsDone > size(tube_journey) ) 
                          THEN
                                 journey :=  NO_JOURNEY_LEFT   ||
                                 report      :=  ERROR_Journey_Not_That_Long
                          END
                            
                    END
                                
       
END