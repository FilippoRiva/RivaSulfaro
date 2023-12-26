//Each team has a unique battle rank within a Kata Battle
assert UniqueBattleRank {
    all kb : KataBattle | all t1, t2 : getTeams[kb] |
        (t1.battleRank = t2.battleRank) implies (t1 = t2)
}

//A KTRank's rank is within the correct range
assert KTRankWithinRange {
    all ktr : KTRank | ktr.ktRank >= 1 and ktr.ktRank <= #(getKTRanks[ktr.tournament])
}

//Each team has a unique Git repository
assert UniqueGitHubRepoForTeams {
    all t1, t2 : Team | (t1.gitHubRepoTeam = t2.gitHubRepoTeam) implies (t1 = t2)
}

//A student can be subscribed to a tournament only if they have a KTRank
assert SubscriptionOnlyIfKTRank {
    all s : Student, kt : KataTournament |
        isSubscribed[s, kt] implies some ktr : KTRank | ktr.student = s and ktr.tournament = kt
}

//Each KT rank is unique within a tournament
assert UniqueKTRankWithinTournament {
    all kt : KataTournament |
        all ktr1, ktr2 : getKTRanks[kt] | (ktr1.ktRank = ktr2.ktRank) implies (ktr1 = ktr2)
}