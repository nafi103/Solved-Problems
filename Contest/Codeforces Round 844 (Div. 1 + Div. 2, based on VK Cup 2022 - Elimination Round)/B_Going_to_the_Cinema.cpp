#include<bits/stdc++.h>
using namespace std;
 int main(){
    int t;
    cin>>t;
    while(t--){
        int n,cnt=0;
        cin>>n;
        vector<int>v(n+1);
        v[0]=-1;
        for(int i=1;i<=n;i++){
            cin>>v[i];
        }
        sort(v.begin()+1,v.end());
        for (int i = 1; i <=n; i++)
        {
            if(v[i]<i&&(i==n||v[i+1]>i))    cnt++;
        }
        if(v[1]!=0) cnt++;
        cout<<cnt<<endl;
    }
}