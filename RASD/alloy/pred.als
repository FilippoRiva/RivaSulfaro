//return true is the Student s is subscribed to the KataTournament kt2
pred isSubscribed [s : Student, kt2 : KataTournament] {
	some t : getTeams[s] | t.kb.kt = kt2
}