#include <bits/stdc++.h>
#define ll long long
using namespace std;
  int main(){
    int t;
    cin>>t;
    while(t--){
        ll n;
        cin>>n;
        vector<ll>v1,v2;
        for(int i=0;i<n;i++){
            int x;
            cin>>x;
            v1.push_back(x);
            v2.push_back(x);
        }
        sort(v1.begin(),v1.end());
        for (int i = 0; i < v2.size(); i++)
        {
            if(v2[i]==v1[n-1])  cout<<v2[i]-v1[n-2]<<" ";
            else cout<<v2[i]-v1[n-1]<<" ";
        }
        cout<<endl;
    }
}