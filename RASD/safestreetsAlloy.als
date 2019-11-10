//================================================================
//====================== PRIMITIVE SIGNATURES =========================

sig Name {}

sig Surname {}

sig Email {}

sig Address {}

sig FIN {}

sig Double {}

sig CarModel {} 

sig CarPlate {}

enum Status {
			Open,
			Closed
			}

//================================================================
//========================== SIGNATURES ============================

sig Day { Value: Int } {Value>0}

sig Time { hours: Int,
				minutes: Int
				} {hours >0 and minutes>0}

sig Person  { name: Name,
				surname: Surname,
				email: Email,
				isUser: lone User,
				isAuthority: lone Authority
				}

some sig  User { name: Name,
				surname: Surname,
				email: Email,
				createsReport: set Report,
				currentlyAtPos: Position
				}

some sig  Authority { name:one Name,
					   surname:one Surname,
					   email:one Email,
					   fin:one FIN,
					   currentlyAtPos: Position,
					   allReports: set Report
					   }

sig Position { address: one Address,
					  latitude: one Double,
					  longitude: one Double
					  }

some sig Report { day:  Day,
					time:  Time,
					creator: one User,
					carModel: lone CarModel,
					position:  Position,
					carPlate:  CarPlate,
					violation:  TrafficViolation,
					status: one Status
					} 


abstract sig TrafficViolation{}

sig ParkingViolation extends TrafficViolation {}

sig SpeedViolation extends TrafficViolation {}

//================================================================
//========================== FACT ===========================

fact AllPersonAreOrAnAuthorityOrAUser
{
all p : Person | (p.isUser = User and p.isAuthority = none) or (p.isAuthority = Authority and p.isUser = none)
}


fact EveryUserHas2Person
{
all u : User | some disj p1,p2 : Person | p1.isUser = u => p1.isAuthority = none and samePerson[p1,p2]
}

fact EveryAuthorityHas2Person
{
all a : Authority | some disj p1,p2 : Person |  p1.isAuthority = a => p1.isUser = none and samePerson[p1,p2]
}

fact SameEmailImpliesSamePerson
{
 all p1,p2 : Person | p1.email = p2.email => (samePerson[p1,p2]) 
}

fact AllNameMustBelongToSomeone
{
all n : Name | some u : User, a : Authority | (a.name = n) or (u.name = n) 
}

fact AllSurameMustBelongToSomeone
{
all s : Surname | some u : User, a : Authority | (a.surname = s) or (u.surname = s) 
}

fact AllEmailMustBelongToSomeone
{
all e : Email | some  u : User, a : Authority | (u.email = e) or (a.email = e)
}

fact noMailShared
{
 all u : User, a : Authority | (u.email != a.email)
}

fact AllAddressesMustBelongToPositions 
{
all a : Address | some pos : Position | pos.address = a
}

fact eachUserIsUnique
{
 all disj  u1 , u2 : User |  (u1.name != u2.name ) and (u1.email != u2.email) and (u1.surname !=u2.surname)
}

fact eachAuthorityIsUnique
{
	all disj a1 , a2: Authority | (a1.fin != a2.fin) and (a1.email != a2.email) 
}

fact authorityHaveAccessToAllTheReports
{
 all r : Report , a : Authority | (r in a.allReports)
}


 fact justOneReportOfTheSameViolationPerDayReferringToTheSameCar 
{
	all disj r1,r2 : Report |  ( r1.day != r2.day) and (r1.violation != r2.violation) and (r1.carPlate != r2.carPlate) and (r1.position != r2.position)
}

fact SameCarCommitsMultipleViolationAfterAtLeast5Minutes
{
 all disj r1, r2 : Report | ((r1.day = r2.day)and(r1.carPlate = r2.carPlate)and(r1.violation != r2.violation)) =>( ((r2.time.minutes - r1.time.minutes) > 4)or((r1.time.minutes - r1.time.minutes) > 4))
}

fact justOneCreatorForReport
{
 all r : Report, u : User | ( u.createsReport = r) <=> (r.creator = u)
}

fact compleatePosition 
{
 all disj p1,p2 : Position |  (p1.address != p2.address) and (p1.latitude != p2.latitude and p1.longitude != p2.longitude)
}




//================================================================
//===========================ASSERTION=============================

assert user_consistency
{
no disj u1,u2 : User  |   (u1.name = u2.name ) and(u1.email = u2.email) and(u1.surname = u2.surname)
}

//check user_consistency

assert authority_consistency
{
	no disj a1 , a2: Authority | (a1.fin = a2.fin) and (a1.email = a2.email) 
}

check authority_consistency

assert justOneReport
{
	no disj r1,r2 : Report |  ( r1.day = r2.day) and (r1.violation = r2.violation) and (r1.carPlate = r2.carPlate) and (r1.position = r2.position)
}

check justOneReport



//================================================================
//===========================PREDICATES============================
pred samePerson[p1,p2 : Person] 
{
p1.email = p2.email and p1.name = p2.name and p1. surname = p2.surname
}

pred showAllReportsClosed
{
some r : Report | r.status= Closed
}

run showAllReportsClosed

pred showAllReportsOpen
{
some r : Report | r.status= Open
}

run showAllReportsOpen

pred showAllUserThatSendReports
{
some r : Report | r.creator = User
}

run showAllUserThatSendReports

pred show { }

run show
