#include<bits/stdc++.h>
using namespace std;
const int mod = 1e9+7;
int countWays(vector<int>&a,int t){
    vector<int>dp(t+1,0);
    dp[0] = 1;
    for(auto &x: a){
        for(int i = 0; i+x<=t; i++){
            dp[i+x] = (dp[i+x]+dp[i])%mod;
        }
    }
    return dp[t];
}