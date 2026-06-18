#include<bits/stdc++.h>
#define ll long long
using namespace std;
  int main(){
    int t;
    cin>>t;
    while(t--){
        ll n,sum = 0, mx=INT_MIN;
        cin>>n;
        int a[n],b[n];
        for (int i = 0; i < n; i++)
        {
            cin>>a[i];
            sum+=a[i];
        }
        for (int i = 0; i < n; i++)
        {
            cin>>b[i];
            sum+=b[i];
            if(mx<b[i]){
                mx=b[i];
            }
        }
        cout<<sum-mx<<endl;
    }
}