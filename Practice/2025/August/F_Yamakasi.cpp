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

struct S{
    int value;

    S(int val = -inf) : value(val) {}

    void read(){
        cin>>value;
    }
};

S combine(S &a, S &b){
    return S(max(a.value,b.value));
}

struct Segment_Tree{
    int n;
    vector<S>t;

    Segment_Tree(vector<int>&v , int _n){
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
    int n,s,x,ans = 0;
    cin>>n>>s>>x;
    vector<int>v(n),pref(n+1,0);
    readv(v);
    Segment_Tree st(v,n);
    map<int,vector<int>>mp;
    mp[0].push_back(0);
    for(int i = 1; i<=n; i++){
        pref[i] = pref[i-1] + v[i-1];
        int to_find = pref[i] - s;
        if(mp.count(to_find)==0){
            mp[pref[i]].push_back(i);
            continue;
        }
        vector<int> &tmp = mp[to_find];
        int left = -1, right = -2, l = 0, r = sz(tmp) - 1;
        while(l<=r){
            int mid = (l+r)/2;
            if(st.query(tmp[mid],i).value>x){
                l = mid+1;
            }else{
                r = mid-1;
            }
        }
        if(l<sz(tmp)){
            left = l;
            l = 0; r = sz(tmp)-1;
            while(l<=r){
                int mid = (l+r)/2;
                if(st.query(tmp[mid],i).value>=x){
                    l = mid+1;
                }else{
                    r = mid-1;
                }
            }
            right = l;
            ans+=max(0ll,right-left);
        }
        mp[pref[i]].push_back(i);
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