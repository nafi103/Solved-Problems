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
const int N = 2e5+1;
vector<int>cnt(N),pcnt(N);

void solve()
{
    int n,y, ans = -inf;
    cin>>n>>y;
    for(int i = 0; i<N; i++)
        cnt[i] = pcnt[i] = 0;
    for(int i = 0; i<n; i++){
        int x;
        cin>>x;
        cnt[x]++;
        pcnt[x]++;
    }
    for(int i = 1; i<N; i++)
        pcnt[i]+=pcnt[i-1];
    for(int x = 2; x<N; x++){
        int curr_ans = -n*y;
        for(int i = 0; i<N; i+=x){
            int c = pcnt[min(i+x,N-1)] - pcnt[i];
            curr_ans += c*(i/x+1) + y*(min(c,cnt[i/x+1]));
        }
        ans = max(ans,curr_ans);
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
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}