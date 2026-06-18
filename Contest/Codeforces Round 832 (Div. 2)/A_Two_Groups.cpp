#include<bits/stdc++.h>
#define ll long long
using namespace std;
 int main(){
    int t;
    cin>>t;
    while(t--){
        ll n,x;
        cin>>n;
        vector<ll> v1,v2;
        v1.push_back(0);
        v2.push_back(0);
        for(int i = 0; i<n;i++){
            cin>>x;
            if(x>0) v1.push_back(x);
            else    v2.push_back(x);
        }
        ll sum1=0,sum2=0;
        for(int i = 0; i<v1.size();i++){
            sum1+=v1[i];
        }
        for(int i = 0; i<v2.size();i++){
            sum2+=v2[i];
        }
        if(abs(sum1)>abs(sum2)) cout<<abs(sum1)-abs(sum2)<<endl;
        else    cout<<abs(sum2)-abs(sum1)<<endl;
    }
}