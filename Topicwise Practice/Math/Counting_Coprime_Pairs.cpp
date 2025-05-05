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

const int N = 1e6+10;
vector<pair<int,int>>nums;

void find_nums(int value, int pos, int taken,vector<int>&primes){
    if(pos==sz(primes)){
        if(value>1){
            nums.push_back({value,taken});
        }
        return;
    }
    if(value*primes[pos]<N)
        find_nums(value*primes[pos],pos+1,taken+1,primes);
    find_nums(value,pos+1,taken,primes);
}

void solve()
{
    int n;
    cin>>n;
    int final_ans  = (n*(n-1))/2,rmv = 0;
    vector<vector<int>>dist_primes(N);
    for(int i = 2; i<N; i++){
        if(dist_primes[i].empty()){
            for(int j = i; j<N; j+=i){
                dist_primes[j].push_back(i);
            }
        }
    }
    vector<int>cnt(N,0),multiple(N,0);
    for(int i = 0; i<n; i++){
        int x;
        cin>>x;
        cnt[x]++;
    }
    for(int i = 2; i<N; i++){
        for(int j = i; j<N; j+=i){
            multiple[i]+=cnt[j];
        }
    }
    for(int i = 2; i<N; i++){
        if(cnt[i]){
            int ans = 0;
            nums.clear();
            find_nums(1,0,0,dist_primes[i]);
            debug(i)
            for(auto &[f,s]: nums){
                if(s&1)
                    ans+=multiple[f];
                else{
                    ans-=multiple[f];
                }
            }
            rmv+=(cnt[i]*(ans-1));
        }
    }
    cout<<final_ans - rmv/2<<endl;
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