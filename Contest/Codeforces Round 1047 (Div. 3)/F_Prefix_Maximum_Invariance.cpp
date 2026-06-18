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

struct S{ 
    int value;

    S(int val = -inf) : value(val) {} //if sum set to -> 0, min -> inf, max -> -inf
};

S combine(S &a, S &b){
    return S(max(a.value,b.value)); //change opertation for min,max
}

struct Segment_Tree{
    int n;
    vector<S>t;

    Segment_Tree(vector<int>&v, int _n){
        n = _n;
        t.resize(2*n);
        for(int i = n; i<2*n; i++){
            t[i] = S(v[i-n]);
        }
        build();
    }

    void build(){
        for (int i = n - 1; i > 0; --i) t[i] = combine(t[i<<1], t[i<<1|1]);
    }

    S query(int l, int r) {
        S resl, resr;
        for (l += n, r += n; l < r; l >>= 1, r >>= 1) {
            if (l&1) resl = combine(resl, t[l++]);
            if (r&1) resr = combine(t[--r], resr);
        }
        return combine(resl, resr);
    }
};

void solve()
{
    int n, ans = 0;
    cin>>n;
    vector<int>a(n+1,inf),b(n+1);
    for(int i = 1; i<=n; i++)
        cin>>a[i];
    for(int i = 1; i<=n; i++)
        cin>>b[i];
    Segment_Tree st(a,n+1);
    for(int i = 1; i<=n; i++){
        if(a[i]==b[i]){
            ans+=(i*(n-i+1));
        }else{
            int mx = max(a[i],b[i]),l = 0, r = i-1;
            while(l<=r){
                int mid = (l+r)/2;
                if(st.query(mid,i).value>=mx)
                    l = mid+1;
                else
                    r = mid-1;
            }
            ans+=(r*(n-i+1));
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
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}