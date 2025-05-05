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
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define writev(v)     \
    for (auto &x : v) \
    cout << x << " "; \
    cout<<endl
#define endl "\n"
#define yes cout<<"YES"<<endl
#define no cout<<"NO"<<endl
#define remove_punctuation(text) regex_replace(text, regex(R"([^\w\s])"), "")
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

void solve()
{
    int n,q,m = 6;
    cin>>n>>q;
    string str = "abc";
    vector<string>valid;
    do{
        valid.pb(str);
    }while(next_permutation(all(str)));
    cin>>str;
    for(int i = 0; i<m; i++){
        string curr = valid[i];
        while(sz(valid[i])<=n){
            valid[i]+=curr;
        }
    }
    vector<vector<int>>pref(m);
    for(int i = 0; i<m ; i++){
        pref[i].resize(n+1);
        pref[i][0] = 0;
        for(int j = 1; j<=n; j++){
            pref[i][j] = (valid[i][j]!=str[j-1]);
            pref[i][j]+=pref[i][j-1];
        }
    }
    while(q--){
        int l,r,ans = INT_MAX;
        cin>>l>>r;
        for(int i = 0; i<m; i++){
            ans = min(ans,pref[i][r] - pref[i][l-1]);
        }
        cout<<ans<<endl;
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
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}