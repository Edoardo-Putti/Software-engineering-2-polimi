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

sig Day { Value: Int }

sig Time { hours: Int,
				minutes: Int
				}

sig User { name: Name,
				surname: Surname,
				email: Email,
				createsReport: set Report,
				currentlyAtPos: Position
				}

sig Authority { name: Name,
					   surname: Surname,
					   email: Email,
					   fin: FIN,
					   currentlyAtPos: Position,
					   allReports: set Report
					   }

sig Position { address: one Address,
					  latitude: one Double,
					  longitude: one Double
					  }

sig Report { day:  Day,
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
//========================== CONSISTENCY ===========================

fact authority_consistency
{
	all disj a1 , a2: Authority | (a1.fin != a2.fin) and (a1.email != a2.email) 
}

assert a_consistency
{
	no disj a1 , a2: Authority | (a1.fin = a2.fin) and (a1.email = a2.email) 
}
//================================================================
fact user_consistency
{
 all disj  u1 , u2 : User |  (u1.name != u2.name ) and (u1.email != u2.email) and (u1.surname !=u2.surname)
}

assert u_consistency
{
no disj u1,u2 : User  |   (u1.name = u2.name ) and(u1.email = u2.email) and(u1.surname = u2.surname)
}

//check consistency

//================================================================
assert justOneReport 
{
	no disj r1,r2 : Report |  ( r1.day = r2.day) and (r1.violation = r2.violation) and (r1.carPlate = r2.carPlate) and (r1.position = r2.position)
}

 fact justOneReportOfTheSameViolationPerDay 
{
	all disj r1,r2 : Report |  ( r1.day != r2.day) and (r1.violation != r2.violation) and (r1.carPlate != r2.carPlate) and (r1.position != r2.position)
}

fact SameCarCommitsMultipleViolation
{
 all disj r1, r2 : Report | ((r1.day = r2.day)and(r1.carPlate = r2.carPlate)and(r1.violation != r2.violation)) => (r2.time.minutes - r1.time.minutes > 4)
}

fact justOneCreator
{
 all disj r1, r2 : Report, u1, u2 : User | (r1.creator != r2.creator)
}
//check justOneR
//================================================================
fact noMailShared
{
 all u : User, a : Authority | (u.email != a.email)
}
//================================================================
fact compleatePosition 
{
 all disj p1,p2 : Position |  (p1.address != p2.address) and (p1.latitude != p2.latitude and p1.longitude != p2.longitude)
}


pred show {}
run show {}
