MACHINE  Family
    
  SETS
    PEOPLE = { Grandad, Paul, Jim, Mary, Ian, 
    	       Jack, Jill, Jane, Bill, Joe    } ;
    
    SEX =  { Male, Female, Trans } ;
          
    REPORT =  {  
    	         Success, 
                 Error_NotAFamilyMembersDeath, 
		 Error_NotAFamilyMembersBirthday, 
                 Error_NotAFamilyMembersBaby,  
		 Error_MalesCantHaveBabies, 
                 Error_AlreadyUsedName,
		 Error_MotherTooYoung  
	      } ;

    ANSWER =   { Yes_Someone_Has_This_Sex, No_One_Has_This_Sex  };
    
    // Exercises 6.7 & 6.8     
	PASSPORT_REPORT = { PassportGranted_Success, 
	                    Passport_ERROR_Person_not_Family,
	                    Passport_ERROR_Person_Already_Has_Passport,
	                    Passport_ERROR_Number_Already_Used,
	                    
	                    PassportRenewed_Success,
	                    Passport_ERROR_Person_Has_No_Passport,
	                    Passport_ERROR_New_Number_Already_Used
	                  } ;

  	// Exercises 6.7 & 6.8     
    PARENT_ANSWER = { Yes, No, Do_Not_Know } 
    
  CONSTANTS
    PASSPORT_NUMBER,
    MinimumMumAge 

  PROPERTIES
    PASSPORT_NUMBER = NAT1
    &
    MinimumMumAge : NAT1 &  MinimumMumAge = 16

  
  VARIABLES
    family,
    age,
    sex,
    passportNumber,          // Exercise 6.4
    parentOf,                // Exercise 6.5
    myMum                    // Exercise 6.6
  
  INVARIANT
    family  <: PEOPLE      &
    age : PEOPLE +-> NAT   &  dom(age) = family  &
    sex : PEOPLE +-> SEX   &  dom(sex) = family          
    &
    passportNumber : PEOPLE >+> PASSPORT_NUMBER  &      // Exercise 6.4
    dom( passportNumber ) <: family                     
    
    &
    parentOf : PEOPLE <-> PEOPLE  &                     // Exercise 6.5
    dom( parentOf ) <: family     &                     
    ran( parentOf ) <: family                          
    
    &
    myMum : PEOPLE +-> PEOPLE  &                        // Exercise 6.6
    dom( myMum ) <: family     &                        
    ran( myMum ) <: family                              

  INITIALISATION
       family := { Grandad, Paul, Mary, Jim, Jane, Jill }  
    ||
       age    := { Grandad |-> 100, Paul |-> 41,  Jim |-> 15, 
                      Jane |-> 11,  Mary |-> 40, Jill |-> 4   }  
    ||
       sex    := { Paul |-> Male,   Mary |-> Female,     Jim |-> Male,
                   Jane |-> Female, Jill |-> Female, Grandad |-> Male  }  
  ||
       passportNumber := {}                 // Exercise 6.4: no one initially has a passport
  
    ||
       parentOf := { Grandad |-> Paul,      // Exercise 6.5: family tree relationship
                     Grandad |-> Mary,      // Paul & Mary are siblings,
                     Paul    |-> Jane,      // Paul has a daughter Jane
                     Mary    |-> Joe,       // Mary has a son Joe & daughter Jill
                     Mary    |-> Jill
                   }
  
    ||
       myMum := { Joe  |-> Mary,            // Exercise 6.6: 
                  Jill |-> Mary             // Mary is Joe's & Jill's mum
                }

  
  
  OPERATIONS
    
    report <-- HadBirthday( person ) =
               PRE
                   person : PEOPLE
               THEN
                   IF   ( person : family )
                   THEN
                         age    := age <+ { person |-> (age(person) + 1) }  ||
                         report := Success
                   ELSE 
                         /* ( person /: family ) */
                         report := Error_NotAFamilyMembersBirthday
                   END
               END ;
              
              
    report <-- PersonDies( person ) =
              PRE
                  person : PEOPLE
              THEN
                  IF   ( person : family )
                  THEN
                        family  := family - { person }  ||
                        age     := { person } <<| age   ||
                        sex     := { person } <<| sex   ||
                        report  := Success
                  ELSE 
                        /* ( person /: family ) */
                        report := Error_NotAFamilyMembersDeath
                  END
              END ;
                      
                      
    report <-- HadABaby( mother, baby, babysex ) =
              PRE
                  ( mother : PEOPLE & baby : PEOPLE & babysex : SEX )
              THEN
                  IF   ( mother : family              &  
                         sex(mother) = Female         &
                         age(mother) >= MinimumMumAge &
                         baby /: family                  )
                  THEN
                        family  := family \/ { baby }          ||
                        age     := age \/ { baby |-> 0 }       ||
                        sex     := sex \/ { baby |-> babysex } ||
                        report  := Success
                  ELSIF
                        ( mother /: family )
                  THEN
                        report := Error_NotAFamilyMembersBaby 
                  ELSIF
                        ( sex(mother) = Male )
                  THEN
                        report := Error_MalesCantHaveBabies
                  ELSIF
                        ( age(mother) < MinimumMumAge )
                  THEN
                         report := Error_MotherTooYoung
                  ELSE
                         /* baby : family */
                         report := Error_AlreadyUsedName
                       
                  END
              END ;
                      
   
    answer <-- DoesAFamilyMemberHaveThisSex( ss ) =
               PRE 
                    ( ss : SEX  & answer : ANSWER )
               THEN
                   IF   ( ss : ran(sex) )
                   THEN
                         answer := Yes_Someone_Has_This_Sex
                   ELSE 
                         /* ( ss /: ran(sex) ) */
                         answer := No_One_Has_This_Sex  
                   END
               END; 

     // Exercise 6.7
     
     report <-- FirstPassport( person, passportNum ) =
                  PRE
                        person      : PEOPLE &
                        passportNum : PASSPORT_NUMBER &
                        report      : PASSPORT_REPORT
                  THEN
                          IF   ( person : family  &  
                                 person /: dom( passportNumber )   &
                                 passportNum /: ran( passportNumber ) ) 
                          THEN
                                   passportNumber := passportNumber \/ { person |-> passportNum } 
                                || 
                                   report := PassportGranted_Success

                          ELSIF  ( person /: family ) 
                          THEN
                                 report := Passport_ERROR_Person_not_Family
                                   
                          ELSIF  ( person : dom( passportNumber ) ) 
                          THEN
                                 report := Passport_ERROR_Person_Already_Has_Passport

                          ELSIF  ( passportNum : ran( passportNumber ) ) 
                          THEN
                                 report := Passport_ERROR_Number_Already_Used
                          END
                      
                  END
                  ;
                  
               
     // Exercise 6.8
     
     report <-- RenewPassport( person, newPassportNum ) =
                  PRE
                        person         : PEOPLE &
                        newPassportNum : PASSPORT_NUMBER &
                        report         : PASSPORT_REPORT
                  THEN
                          IF   ( person : family  &  
                                 person : dom( passportNumber )   &
                                 newPassportNum /: ran( passportNumber ) ) 
                          THEN
                                   passportNumber := passportNumber <+ { person |-> newPassportNum } 
                                || 
                                   report := PassportRenewed_Success

                          ELSIF  ( person /: family ) 
                          THEN
                                 report := Passport_ERROR_Person_not_Family
                                   
                          ELSIF  ( person /: dom( passportNumber ) ) 
                          THEN
                                 report := Passport_ERROR_Person_Has_No_Passport

                          ELSIF  ( newPassportNum : ran( passportNumber ) ) 
                          THEN
                                 report := Passport_ERROR_New_Number_Already_Used
                          END
                      
                  END
		  ;
       
       
    
	 // Exercise 6.9       
	 
	 answer <-- HasChildren( person ) = 
                  PRE
                        person : PEOPLE &
                        answer : PARENT_ANSWER
                  THEN
                        IF    ( person : family  &  
                                person : dom( parentOf )  ) 
                        THEN
                               answer := Yes
                               
                        ELSIF  ( person : family  &  
                                 person /: dom( parentOf )  ) 
                        THEN     
                               answer := No
                               
                        ELSIF  ( person /: family ) 
                        THEN     
                                answer := Do_Not_Know
                        END
                  END
                    

END 