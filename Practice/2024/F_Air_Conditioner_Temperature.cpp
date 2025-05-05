#include<bits/stdc++.h>
using namespace std;

void solve(){
    int A,B,C;
    cin>>A>>B>>C;
    int L = max(A,C), R = B;
    // I want to find the maximum between A,B,C
    // max({A,B,C......}) min({A,B,C.....})
    if(L<=R){
        cout<<"Yes"<<endl;
    }else{
        cout<<"No"<<endl;
    }
}

int main(){
    int t;
    cin>>t;
    while(t--){
        solve();
    }
}