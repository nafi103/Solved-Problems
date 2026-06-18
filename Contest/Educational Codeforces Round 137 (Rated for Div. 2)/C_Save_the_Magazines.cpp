#include<bits/stdc++.h>
#define ll long long
#define frn for(int i = 0;i<n;i++)
using namespace std;
 void solution(){
    int n;
    string str;
    cin>>n>>str;
    int arr[n];
    for (int i = 0; i < n; i++)
    {
        cin>>arr[i];
    }
    int p1=0,p2=0;
    for (int i = 0; i < n; i++)
    {
        if(str[i]=='1') p1+=max(arr[i],p2);
        if(str[i]=='0'||arr[i]<p2)  p2=arr[i];
    }
    cout<<p1<<endl;
}
 int main(){
    int t;
    cin>>t;
    while(t--)  solution();
}