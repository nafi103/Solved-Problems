#include<bits/stdc++.h>
using namespace std;
 void solution()
{
    vector<int>v;
    int n,x;
    cin>>n;
    int arr1[n],arr2[n];
    for (int i = 0; i < n; i++) cin>>arr1[i];
    for (int i = 0; i < n; i++) cin>>arr2[i];
    for (int i = 0; i < n; i++)
    {
        x = arr2[i]-arr1[i];
        v.push_back(x);
    }
    sort(v.begin(),v.end(),greater<int>());
    int cnt = 0, p1,p2;
    p1 = 0;
    p2 = v.size()-1;
    while(p1<p2){
        if(v[p1]+v[p2]>=0){
            cnt++;
            p1++;
            p2--;
        }else   p2--;
    }
    cout<<cnt<<endl;
}
 int main(){
    int t;
    cin>>t;
    while(t--)  solution();
}