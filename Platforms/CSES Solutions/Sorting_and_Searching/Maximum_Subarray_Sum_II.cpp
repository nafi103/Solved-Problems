#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

const int inf  = 1e14+10;
#define int long long
#define pi acos(-1.0)
#define mod 998244353
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
#define set_bits(x) __builtin_popcount(x)
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
vector<int>st;
int n,a,b;

void build() {
    for (int i = n - 1; i > 0; --i) st[i] = min(st[i<<1] , st[i<<1|1]);   
}

int query(int l, int r) {
    l = max(l,0ll);
    int res = inf;
    for (l += n, r += n; l < r; l >>= 1, r >>= 1) {
        if (l&1) res = min(res, st[l++]);
        if (r&1) res = min(res, st[--r]);
    }
    return res;
}

void solve()
{
    cin>>n>>a>>b;
    st.resize(2*n);
    for(int i = n; i<2*n; i++){
        cin>>st[i];
        if(i>n) st[i]+=st[i-1];
    }
    build();
    int ans = st[n+a-1];
    for(int j = n+a; j<2*n; j++){
        int l = j-b-n, r = j-a-n+1;
        ans = max(ans, st[j] - min(query(l,r),(l<0ll?0ll:inf)));
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
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}