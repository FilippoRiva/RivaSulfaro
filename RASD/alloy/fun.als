// +--------------------------------------------+
// |                   Utils                    |
// +--------------------------------------------+
//return all the solutions of a Student s in the KataTournament kt2
fun getSolutions [s : Student, kt2 : KataTournament] : TeamKataSolution {
	{ts: TeamKataSolution |some t : getTeams[s] | t.kb.kt = kt2 implies ts = t.solution}
}

//return the total score of a Student s in the KataTournament kt
fun studentScore [s : Student, kt : KataTournament] : Int {
	sum solution : getSolutions[s, kt]  | solution.score
}

// +--------------------------------------------+
// |                   Reverse                  |
// +--------------------------------------------+

//return the teams of a Student s
fun getKTRanks [t : KataTournament] : KTRank {
	{ktr : KTRank | ktr.tournament = t}
}

//return the ktRanks of a Student s
fun getKTRanks [s : Student] : KTRank {
	{ktr : KTRank | ktr.student = s}
}

//return the teams of a Student s
fun getTeams [s : Student] : Team {
	{team : Team | s in team.players}
}

//return the teams of a Student s
fun getTeams [battle : KataBattle] : Team {
	{team : Team | team.kb = battle}
}