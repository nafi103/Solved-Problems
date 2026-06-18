#include<bits/stdc++.h>
#define int long long
using namespace std;
const int N = 2* 1e5 + 10;
vector<int>power(N);
 void l(){
    int n;
    cin>>n;
    int m = 0;
    for (int i = 0; i < n; i++)
    {
        int s;
        cin>>s;
        while(s%2 ==0){
            m++;
            s/=2;
        }
    }
    int o = max(0LL, n-m);
    vector<int>v(n);
    for (int i = 0; i < n; i++)
    {
        v[i]= power[i+1];
    }
    sort(v.rbegin(),v.rend());
    int ans = 0;
    for (int i = 0; i < n; i++)
    {
        if(o<=0)    break;
        ans++;
        o-=v[i];
    }
    if(o>0) cout<<"-1"<<endl;
    else    cout<<ans<<endl;
}
 int32_t main(){
    for (int i = 1; i < N; i++)
    {
        int k = 0;
        int x = i;
        while(x%2==0){
            k++;
            x/=2;
        }
        power[i]= k;
    }
    int t;
    cin>>t;
    while (t--)
    {
        l();
    }
}