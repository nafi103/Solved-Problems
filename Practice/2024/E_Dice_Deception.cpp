#include<bits/stdc++.h>
using namespace std;

void solve(){
    int N,K;
    cin>>N>>K;
    vector<int> diceRoll(N);
    int score = 0;
    for(int i = 0; i<N; i++){
        cin>>diceRoll[i];
    }
    sort(diceRoll.begin(),diceRoll.end());
    for(int i = 0; i<N; i++){
        if(K>0){
            int opposite = 7-diceRoll[i];
            if(opposite>diceRoll[i]){
                score+=opposite;
                K--;
            }else{
                score+=diceRoll[i];
            }
        }else{
            score+=diceRoll[i];
        }
    }
    cout<<score<<endl;
}

int main(){
    int t;
    cin>>t;
    while(t--) solve();
}