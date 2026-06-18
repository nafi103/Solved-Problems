#include<bits/stdc++.h>
using namespace std;
 void solution(){
    int n,mn = INT_MAX;
    cin>>n;
    vector<int>v,v1;
    for (int i = 0; i < n; i++)
    {
        int x;
        cin>>x;
        v.push_back(x);
    }
    sort(v.begin(),v.end());
    for (int i = 0; i < v.size(); i++)
    {
        if(i>0){
            v1.push_back(v[i]-v[i-1]);
        }
    }
    for(int i = 1;i<v1.size();i++){
        if(v1[i]+v1[i-1]<mn)    mn = v1[i]+v1[i-1];
    }
    cout<<mn<<endl;
}
 int main(){
    int t;
    cin>>t;
    while(t--)  solution();
}