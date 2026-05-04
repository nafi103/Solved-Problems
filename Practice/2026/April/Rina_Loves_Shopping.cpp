#include<bits/stdc++.h>
using namespace std;
#define int long long
int n,x,sum,mx;
int32_t main(){
int t=1;cin>>t;while(t--){cin>>n;sum=0,mx=-LLONG_MAX;
for(int i=0;i<n;i++){cin>>x;sum+=x;mx=max(sum,mx);if(sum<0)sum = 0;}cout<<mx<<'\n';}}