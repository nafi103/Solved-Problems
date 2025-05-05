#include<bits/stdc++.h>
using namespace std;

void solve(){
    int N,X,Y;
    cin>>N>>X>>Y;
    vector<int> pokemon(N);
    for(int i = 0; i<N; i++){
        cin>>pokemon[i];
    }
    int cost = 0;
    for(int i = 0; i<N; i++){
        int costOfNormalPokeball = pokemon[i]*X;
        cost += min(costOfNormalPokeball,Y);
    }
    cout<<cost<<endl;
}

int main(){
    int t;
    cin>>t;
    while(t--) solve();
}