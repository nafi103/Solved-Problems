#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18+10
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define endl "\n"
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/
const int N = 2e5+2;
int n;
int next_zero[N],dp[N][2];
char v[N];

int f(int i, int d){
    if(i==n)
        return 1;
    int &ans = dp[i][d];
    if(ans!=-1)
        return ans;
    ans = 0;
    int ni = next_zero[i];
    if(d==0){
        ans = f(ni,1);
        if(ni-i==1)
            ans|=f(ni,0);
    }else{
        if(ni==i+1)
            ans|=(f(ni,1)|f(ni,0));
        else{
            if(ni-i==2 and ni!=n)
                ans = f(ni,0);
        }
    }
    return ans;
}


void solve()
{
    cin>>n;
    for(int i = 0; i<n; i++){
        dp[i][0] = dp[i][1] = -1;
        cin>>v[i];
    }
    int nz = n;
    for(int i = n-1; i>=0; i--){
        next_zero[i] = nz;
        if(v[i]=='0')
            nz = i;
    }
    int start = (v[0]=='0'?0:next_zero[0]);
    if(f(start,1) or (start==0 and f(0,0))){
        cout<<"YES"<<endl;
    }
    else{
        cout<<"NO"<<endl;
    }
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}