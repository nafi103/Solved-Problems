#include<bits/stdc++.h>
using namespace std;

void solve(){
    int N, X;
    cin>>N>>X;
    if(X>=N){
        cout<<0<<endl;
        return;
    }
    int Extra = N-X;
    int totalPacketsNeeded = (Extra/4);
    if(Extra%4>0) totalPacketsNeeded++;
    cout<<totalPacketsNeeded<<endl;
}

int main(){
    int t;
    cin>>t;
    while(t--){
        solve();
    }
}