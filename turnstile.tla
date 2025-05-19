----------------------------- MODULE turnstile -----------------------------
EXTENDS Integers, TLC

CONSTANT
    PassTime,
    MaxRidesNum,
    UseTimes

(*--algorithm turnstile
variables
    accessAllowed = FALSE,
    accessDenied = TRUE,
    locked = TRUE,
    timer = 0,
    cardValid \in {TRUE, FALSE};
    rides \in 0..MaxRidesNum;
    counter = 0;

define
    CardStillValid == cardValid
    RidesAvailable == rides > 0
    AccessGranted == CardStillValid /\ RidesAvailable
    TimerExpired == timer >= PassTime
    
    TypeInvariant == /\ cardValid \in BOOLEAN
                     /\ accessAllowed \in BOOLEAN
                     /\ accessDenied \in BOOLEAN
                     /\ locked \in BOOLEAN
                     /\ timer \in 0..PassTime
                     /\ rides \in 0..MaxRidesNum
                     /\ counter \in 0..UseTimes
    
    TurstileWorkEnd == counter >= UseTimes

    \* The two indicators are never both active or both inactive
    IndicatorsMutualExclusive ==
        (accessAllowed /\ ~accessDenied) \/ (~accessAllowed /\ accessDenied)
    
    \* The lock is only open (unlocked) when access is allowed
    LockFollowsAccess ==
        locked = ~accessAllowed
    
    \* Timer is only non-zero if access is allowed (i.e., during access window)
    TimerImpliesAccess ==
        (timer > 0) => accessAllowed
    
    \* When timer is zero, the system must be in the initial (locked) state
    TimerZeroImpliesInitialState ==
        (timer = 0) => /\ accessAllowed = FALSE
                       /\ accessDenied = TRUE
                       /\ locked = TRUE
    
    \* Rides are never negative
    RidesNonNegative ==
        rides >= 0
    
    \* A valid card always has at least one ride if ValidCard is true
    ValidCardMeansRidesPositive ==
        cardValid = TRUE => (AccessGranted <=> rides > 0)
    
    \* If the card is invalid or has no rides left, then the system remains in its initial/locked state
    InvalidCardStateUnchanged ==
        (~cardValid \/ (rides = 0 /\ timer = 0)) =>В
            /\ accessAllowed = FALSE
            /\ accessDenied = TRUE
            /\ locked = TRUE
            /\ timer = 0
end define;

process timer_process = "Timer"
begin
    TimerLoop:
        while (~TurstileWorkEnd) do
            IncrementTimer:
                if timer > 0 then
                        timer := timer + 1;
                end if;
            ResetSystem:
                if TimerExpired then
                        accessAllowed := FALSE;
                        accessDenied := TRUE;
                        locked := TRUE;
                        timer := 0;
                end if;
            WaitForTimerOrAccess:
                await timer > 0 \/ ~AccessGranted \/ TurstileWorkEnd;
        end while;
end process;

process user_process = "User"
begin
    UserActions:
        while (counter < UseTimes) do
            either
                \* Tap valid card with rides
                ValidCardTap:
                    with rides_num \in 1..MaxRidesNum do
                        cardValid := TRUE;
                        rides := rides_num;
                        counter := counter + 1;
                    end with;
            or
                \* Tap expired card
                InvalidCardTap:
                    with rides_num \in 1..MaxRidesNum do
                        cardValid := FALSE;
                        rides := rides_num;
                        counter := counter + 1;
                        skip;
                    end with;
            or
                \* Tap card with no rides
                InvalidCardTapDueToRides:
                    cardValid := TRUE;
                    rides := 0;
                    counter := counter + 1;
                    skip;
            end either;
            
            \* Process card tap
            GrantAccess:
                if AccessGranted then
                        rides := rides - 1;
                        accessAllowed := TRUE;
                        accessDenied := FALSE;
                        locked := FALSE;
                        timer := 1;
                end if;
            
            \* Wait for system to reset before next action
            WaitForReset:
                await locked \/ TurstileWorkEnd;
        end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "bfa04102" /\ chksum(tla) = "4a327817")
VARIABLES accessAllowed, accessDenied, locked, timer, cardValid, rides, 
          counter, pc

(* define statement *)
CardStillValid == cardValid
RidesAvailable == rides > 0
AccessGranted == CardStillValid /\ RidesAvailable
TimerExpired == timer >= PassTime

TypeInvariant == /\ cardValid \in BOOLEAN
                 /\ accessAllowed \in BOOLEAN
                 /\ accessDenied \in BOOLEAN
                 /\ locked \in BOOLEAN
                 /\ timer \in 0..PassTime
                 /\ rides \in 0..MaxRidesNum
                 /\ counter \in 0..UseTimes

TurstileWorkEnd == counter >= UseTimes


IndicatorsMutualExclusive ==
    (accessAllowed /\ ~accessDenied) \/ (~accessAllowed /\ accessDenied)


LockFollowsAccess ==
    locked = ~accessAllowed


TimerImpliesAccess ==
    (timer > 0) => accessAllowed


TimerZeroImpliesInitialState ==
    (timer = 0) => /\ accessAllowed = FALSE
                   /\ accessDenied = TRUE
                   /\ locked = TRUE


RidesNonNegative ==
    rides >= 0


ValidCardMeansRidesPositive ==
    cardValid = TRUE => (AccessGranted <=> rides > 0)


InvalidCardStateUnchanged ==
    (~cardValid \/ (rides = 0 /\ timer = 0)) =>
        /\ accessAllowed = FALSE
        /\ accessDenied = TRUE
        /\ locked = TRUE
        /\ timer = 0


vars == << accessAllowed, accessDenied, locked, timer, cardValid, rides, 
           counter, pc >>

ProcSet == {"Timer"} \cup {"User"}

Init == (* Global variables *)
        /\ accessAllowed = FALSE
        /\ accessDenied = TRUE
        /\ locked = TRUE
        /\ timer = 0
        /\ cardValid \in {TRUE, FALSE}
        /\ rides \in 0..MaxRidesNum
        /\ counter = 0
        /\ pc = [self \in ProcSet |-> CASE self = "Timer" -> "TimerLoop"
                                        [] self = "User" -> "UserActions"]

TimerLoop == /\ pc["Timer"] = "TimerLoop"
             /\ IF (~TurstileWorkEnd)
                   THEN /\ pc' = [pc EXCEPT !["Timer"] = "IncrementTimer"]
                   ELSE /\ pc' = [pc EXCEPT !["Timer"] = "Done"]
             /\ UNCHANGED << accessAllowed, accessDenied, locked, timer, 
                             cardValid, rides, counter >>

IncrementTimer == /\ pc["Timer"] = "IncrementTimer"
                  /\ IF timer > 0
                        THEN /\ timer' = timer + 1
                        ELSE /\ TRUE
                             /\ timer' = timer
                  /\ pc' = [pc EXCEPT !["Timer"] = "ResetSystem"]
                  /\ UNCHANGED << accessAllowed, accessDenied, locked, 
                                  cardValid, rides, counter >>

ResetSystem == /\ pc["Timer"] = "ResetSystem"
               /\ IF TimerExpired
                     THEN /\ accessAllowed' = FALSE
                          /\ accessDenied' = TRUE
                          /\ locked' = TRUE
                          /\ timer' = 0
                     ELSE /\ TRUE
                          /\ UNCHANGED << accessAllowed, accessDenied, locked, 
                                          timer >>
               /\ pc' = [pc EXCEPT !["Timer"] = "WaitForTimerOrAccess"]
               /\ UNCHANGED << cardValid, rides, counter >>

WaitForTimerOrAccess == /\ pc["Timer"] = "WaitForTimerOrAccess"
                        /\ timer > 0 \/ ~AccessGranted \/ TurstileWorkEnd
                        /\ pc' = [pc EXCEPT !["Timer"] = "TimerLoop"]
                        /\ UNCHANGED << accessAllowed, accessDenied, locked, 
                                        timer, cardValid, rides, counter >>

timer_process == TimerLoop \/ IncrementTimer \/ ResetSystem
                    \/ WaitForTimerOrAccess

UserActions == /\ pc["User"] = "UserActions"
               /\ IF (counter < UseTimes)
                     THEN /\ \/ /\ pc' = [pc EXCEPT !["User"] = "ValidCardTap"]
                             \/ /\ pc' = [pc EXCEPT !["User"] = "InvalidCardTap"]
                             \/ /\ pc' = [pc EXCEPT !["User"] = "InvalidCardTapDueToRides"]
                     ELSE /\ pc' = [pc EXCEPT !["User"] = "Done"]
               /\ UNCHANGED << accessAllowed, accessDenied, locked, timer, 
                               cardValid, rides, counter >>

GrantAccess == /\ pc["User"] = "GrantAccess"
               /\ IF AccessGranted
                     THEN /\ rides' = rides - 1
                          /\ accessAllowed' = TRUE
                          /\ accessDenied' = FALSE
                          /\ locked' = FALSE
                          /\ timer' = 1
                     ELSE /\ TRUE
                          /\ UNCHANGED << accessAllowed, accessDenied, locked, 
                                          timer, rides >>
               /\ pc' = [pc EXCEPT !["User"] = "WaitForReset"]
               /\ UNCHANGED << cardValid, counter >>

WaitForReset == /\ pc["User"] = "WaitForReset"
                /\ locked \/ TurstileWorkEnd
                /\ pc' = [pc EXCEPT !["User"] = "UserActions"]
                /\ UNCHANGED << accessAllowed, accessDenied, locked, timer, 
                                cardValid, rides, counter >>

ValidCardTap == /\ pc["User"] = "ValidCardTap"
                /\ \E rides_num \in 1..MaxRidesNum:
                     /\ cardValid' = TRUE
                     /\ rides' = rides_num
                     /\ counter' = counter + 1
                /\ pc' = [pc EXCEPT !["User"] = "GrantAccess"]
                /\ UNCHANGED << accessAllowed, accessDenied, locked, timer >>

InvalidCardTap == /\ pc["User"] = "InvalidCardTap"
                  /\ \E rides_num \in 1..MaxRidesNum:
                       /\ cardValid' = FALSE
                       /\ rides' = rides_num
                       /\ counter' = counter + 1
                       /\ TRUE
                  /\ pc' = [pc EXCEPT !["User"] = "GrantAccess"]
                  /\ UNCHANGED << accessAllowed, accessDenied, locked, timer >>

InvalidCardTapDueToRides == /\ pc["User"] = "InvalidCardTapDueToRides"
                            /\ cardValid' = TRUE
                            /\ rides' = 0
                            /\ counter' = counter + 1
                            /\ TRUE
                            /\ pc' = [pc EXCEPT !["User"] = "GrantAccess"]
                            /\ UNCHANGED << accessAllowed, accessDenied, 
                                            locked, timer >>

user_process == UserActions \/ GrantAccess \/ WaitForReset \/ ValidCardTap
                   \/ InvalidCardTap \/ InvalidCardTapDueToRides

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == timer_process \/ user_process
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Tue May 06 22:30:28 EEST 2025 by Zhenia
\* Created Sat May 03 21:19:27 EEST 2025 by Zhenia
