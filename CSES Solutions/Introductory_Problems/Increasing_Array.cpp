#include <bits/stdc++.h>
#define ll long long
using namespace std;

int main(){
    ll n,cnt = 0;
    cin>>n;
    ll arr[n];
    for(ll i=0; i<n; i++){
        cin>>arr[i];
        if(i==0)    continue;
        if(arr[i]<arr[i-1]){
            cnt+=(arr[i-1]-arr[i]);
            arr[i]=arr[i-1];
        };
    }
    cout<<cnt<<endl;
}