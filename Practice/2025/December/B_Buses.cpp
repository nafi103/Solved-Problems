#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e12 + 10;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

const bool bus = 0, person = 1;

struct Event{
    int s, t;
    bool type;
    Event() : s(0), t(0), type(0){}
    Event(int _s, int _t, bool _type){
        s = _s;
        t = _t;
        type = _type;
    }
};

const Event no_bus = Event(-inf, -inf, 0);

void solve()
{
    int n,m;
    double l, x, y;
    cin >> n >> m >> l >> x >> y;
    vector<Event> events;
    events.reserve(n + m);
    for(int i = 0; i < n; i++){
        int s,t;
        cin >> s >> t;
        events.push_back(Event(s,t,bus));
    }
    for(int i = 0; i < m; i++){
        int m;
        cin >> m;
        events.push_back(Event(m,i,person));
    }
    vector<double> ans(m);
    sort(all(events), [&](const Event &a, const Event &b){
        if(a.s != b.s)
            return a.s < b.s;
        if(a.type != b.type)
            return a.type < b.type;
        return a.t < b.t;
    });
    Event best = no_bus;
    for(auto &curr: events){
        if(curr.type == bus){
            double destination = max(curr.t, best.t);
            double prev_time = ((double)best.t - best.s) / x + (destination - best.t) / y;
            double curr_time = ((double)curr.t - curr.s) / x + (destination - curr.t) / y;
            if(prev_time - curr_time > 0)
                best = curr;
        }else{
            double walk = (l - curr.s) / y;
            double use_bus = ((double)best.t - best.s) / x + (l - best.t) / y;
            ans[curr.t] = min(walk, use_bus);
        }
    }
    for(auto &x: ans)
        cout << x << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    // cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}