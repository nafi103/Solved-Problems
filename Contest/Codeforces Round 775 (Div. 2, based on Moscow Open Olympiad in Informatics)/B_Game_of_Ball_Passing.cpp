#include <bits/stdc++.h>
#define ll long long
using namespace std;
 int main(){
    int t;
    cin>>t;
    while(t--){
        ll n;
        cin>>n;
        vector<int> v;
        long long sum = 0;
        for(int i=0; i<n; i++){
            ll x;
            cin>>x;
            sum += x;
            v.push_back(x);
        }
        sort(v.rbegin(), v.rend());
        ll pass = 2*v[0]-sum;
        if(sum == 0){
            cout<<0<<endl;
        }else if(pass <= 1){
            cout<<1<<endl;
        }else{
            cout<<pass<<endl;
        }
    }
}