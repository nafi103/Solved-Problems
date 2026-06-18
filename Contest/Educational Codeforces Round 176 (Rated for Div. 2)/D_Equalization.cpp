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
#define inf 2e18+10
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

int dp[61][61][63];

int msb(int n){
    if(n==0)
        return -1;
    return 63ll-__builtin_clzll(n);
}

void get_i_j(int &x, int &y, int &i, int &j){
    i = msb(x); j = msb(y);
    while(i>=0 and j>=0 and ((x>>i)&1)==((y>>j)&1)){
        i--;j--;
    }
    i++;j++;
}

int f(int i, int j, int k){
    if(i==0 and j==0)
        return 0;
    if(k==63)
        return inf;
    int &ans = dp[i][j][k];
    if(ans!=-1)
        return ans;
    ans = inf;
    if(i>=k)
        ans = min(ans,(1ll<<k)+f(i-k,j,k+1));
    if(j>=k)
        ans = min(ans,(1ll<<k)+f(i,j-k,k+1));
    ans = min(ans,f(i,j,k+1));
    return ans;
}

void solve()
{
    int x,y;
    cin>>x>>y;
    if(x>y)
        swap(x,y);
    int _x, _y;
    get_i_j(x,y,_x,_y);
    int ans = f(_x,_y,1);
    int msbx = msb(x)+1, msby = msb(y)+1;
    for(int i = 1; i<70; i++){
        int tx = min(msbx,_x+i), ty = min(msby,_y+i);
        ans = min(ans,f(tx,ty,1));
    }
    for(int i = 0; i<30; i++){
        for(int j = 0; j<30; j++){
            ans = min(ans,f(min(msbx+i,60ll), min(msby+j,60ll),1));
        }
    }
    cout<<ans<<endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    memset(dp,-1,sizeof dp);
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}