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

struct Segment{
    int l, r, id;
    void read(int &i){
        cin>>l>>r;
        id = i;
    }
    bool operator==(const Segment &other){
        return l==other.l and r==other.r;
    }
};


void solve()
{
    int n;
    cin>>n;
    vector<Segment>seg(n);
    for(int i = 0; i<n; i++){
        seg[i].read(i);
    }
    sort(all(seg),[&](const Segment &a,const Segment &b){
        if(a.l!=b.l)
            return a.l<b.l;
        return a.r>b.r;
    });
    vector<int>ans(n,0);
    set<int>R,L;
    for(int i = 0; i<n; i++){
        auto rj = R.lower_bound(seg[i].r);
        if(rj!=R.end()){
            ans[seg[i].id]+=(*rj - seg[i].r);
        }
        R.insert(seg[i].r);
    }
    // for(auto &x: seg){
    //     cout<<x.l<<" "<<x.r<<" "<<x.id<<endl;
    // }
    sort(all(seg),[&](const Segment &a,const Segment &b){
        if(a.r!=b.r)
            return a.r>b.r;
        return a.l<b.l;
    });
    for(int i = 0; i<n; i++){
        auto lj = L.upper_bound(seg[i].l);
        if(lj!=L.begin()){
            lj = prev(lj);
            ans[seg[i].id]+=(seg[i].l - *lj);
        }
        if(i and seg[i]==seg[i-1]){
            ans[seg[i-1].id] = 0;
            ans[seg[i].id] = 0;
        }
        L.insert(seg[i].l);
    }
    for(auto &x: ans) cout<<x<<endl;
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
        // google(z);
        solve();
    }
}