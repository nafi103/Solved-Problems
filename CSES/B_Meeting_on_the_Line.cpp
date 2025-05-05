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
const double eps = 1e-7;
int n;
vector<double>cor,ti;
double ans = 0;

bool check(double t){
    double l = -inf, r = inf;
    for(int i = 0; i<n; i++){
        if(t-ti[i]<eps)
            return false;
        double extra = t-ti[i];
        double cl = cor[i]-extra;
        double cr = cor[i]+extra;
        l = max(l,cl);
        r = min(r,cr);
    }
    if(r-l>=eps)
        ans = l;
    return r-l>=eps;
}

double bs(double l, double r){
    if(r-l<=eps){
        return l;
    }
    double mid = (l+r)/2;
    if(check(mid))
        return bs(l,mid-eps);
    return bs(mid+eps,r);
}


void solve()
{
    cor.clear();
    ti.clear();
    cin>>n;
    cor.resize(n);
    ti.resize(n);
    readv(cor);
    readv(ti);
    double l = *max_element(all(ti)), r = 1e8+l;
    bs(l,1e16);
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
        // google(z);
        solve();
    }
}