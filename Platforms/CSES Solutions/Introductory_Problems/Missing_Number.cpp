#include<bits/stdc++.h>
#define ll long long
using namespace std;

int main(){
    ll n,x;
    cin>> n;
    ll sum1 = (n*(n+1))/2, sum2 = 0;
    for(ll i=0; i<n-1; i++){
        cin>>x;
        sum2+=x;
    }
    cout<<sum1-sum2<<endl;
}