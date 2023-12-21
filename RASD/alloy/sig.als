// +--------------------------------------------+
// |                  Utils                     |
// +--------------------------------------------+

// Booleans
abstract sig Boolean {}
lone sig True extends Boolean {}
lone sig False extends Boolean {}

// Date time, represented as an integer
sig DateTime {
    time: one Int
}{
    time >= 0
}

// +--------------------------------------------+
// |                  Attributes                |
// +--------------------------------------------+

sig Email {}{
    one this.~email
}

sig Username {}{
    one this.~username
}

sig Password {}{
    some this.~password
}

sig Description {}

sig GitHubRepo {}

sig Code {}{
    one this.~code
}

// +--------------------------------------------+
// |                   Users                    |
// +--------------------------------------------+

abstract sig User {
    username : disj one Username,
    email : disj one Email,
    password: one Password
}

sig Educator extends User {}

sig Student extends User {}


// +--------------------------------------------+
// |                    CKB                     |
// +--------------------------------------------+

//Ranking of a specif student in a specif KT
//the number is between 1 and the number of student that compete in that KT
sig KTRank {
    ktRank : one Int,
    tournament : one KataTournament,
    student : one Student
}{
    ktRank >= 1 and ktRank <= #(getKTRanks[tournament])
}

//the owner is always an organizer
sig KataTournament {
    owner : one Educator,
    organizers: some Educator,
    descriptionKT : one Description
}{
    owner in organizers
}

//ensure that the score is a positive number
sig TeamKataSolution {
    code : disj one Code,
    score : one Int
}{
    one this.~solution
    one this.~solutions
    score >= 0 //and score <= 100
    //int cannot be that big
}

sig CodeKata {
    solutions : disj set TeamKataSolution,
    descriptionCode : one Description,
    gitHubRepoKata : disj one GitHubRepo
}{
    one this.~code
}

//the number is between 1 and the number of teams that compete in that KB
sig Team {
    players : some Student,
    kb : one KataBattle,
    solution : disj one TeamKataSolution,
    battleRank : one Int,
    gitHubRepoTeam : disj one GitHubRepo
}{
    battleRank >= 1 and battleRank <= #(getTeams[kb])
}

//ensure that a kb has a reasonable number of teamSize and date
sig KataBattle {
    kt : one KataTournament,
    organizer : one Educator,
    code : disj one CodeKata,
    minTeamSize : one Int,
    maxTeamSize : one Int,
    registrationDeadline : one DateTime,
    submissionDeadline : one DateTime,
    isManualEvaluationNeeded : one Boolean
}{
    minTeamSize > 0
    maxTeamSize >= minTeamSize
    submissionDeadline.time > registrationDeadline.time
}
