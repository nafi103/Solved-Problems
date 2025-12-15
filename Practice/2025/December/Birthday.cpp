#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e18 + 10;
const double pi = acos(-1.0);

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

struct Point {
    int x, y;
    bool operator == (Point const& t) const {
        return x == t.x && y == t.y;
    }
};

int orientation(Point a, Point b, Point c) {
    int v = a.x*(b.y-c.y)+b.x*(c.y-a.y)+c.x*(a.y-b.y);
    if (v < 0) return -1;
    if (v > 0) return +1;
    return 0;
}

bool cw(Point a, Point b, Point c, bool include_collinear) {
    int o = orientation(a, b, c);
    return o < 0 || (include_collinear && o == 0);
}
bool collinear(Point a, Point b, Point c) { return orientation(a, b, c) == 0; }

void convex_hull(vector<Point>& a, bool include_collinear = false) {
    Point p0 = *min_element(a.begin(), a.end(), [](Point a, Point b) {
        return make_pair(a.y, a.x) < make_pair(b.y, b.x);
    });
    sort(a.begin(), a.end(), [&p0](const Point& a, const Point& b) {
        int o = orientation(p0, a, b);
        if (o == 0)
            return (p0.x-a.x)*(p0.x-a.x) + (p0.y-a.y)*(p0.y-a.y)
                < (p0.x-b.x)*(p0.x-b.x) + (p0.y-b.y)*(p0.y-b.y);
        return o < 0;
    });
    if (include_collinear) {
        int i = (int)a.size()-1;
        while (i >= 0 && collinear(p0, a[i], a.back())) i--;
        reverse(a.begin()+i+1, a.end());
    }

    vector<Point> st;
    for (int i = 0; i < (int)a.size(); i++) {
        while (st.size() > 1 && !cw(st[st.size()-2], st.back(), a[i], include_collinear))
            st.pop_back();
        st.push_back(a[i]);
    }

    if (include_collinear == false && st.size() == 2 && st[0] == st[1])
        st.pop_back();

    a = st;
}

Point zero(0.0,0.0);

void solve()
{
	double ans = -inf, r;
    int n;
    cin >> n >> r;
    vector<Point> point(n);
    for(auto &p: point){
    	cin >> p.x >> p.y;
    }
    if(n == 1){
    	cout << (pi * r * r) / 2.0 << endl;
    	return;
    }

    double full = (pi * r * r);
    bool flag = false;
    convex_hull(point, false);
    
    for(int i = 0; i < sz(point); i++){
    	Point a = point[i], b = point[(i + 1) % sz(point)];
    	if(cw(b, a, zero, false))
    		flag = true;
    }
    
    if(flag){
    	cout << full / 2.0 << endl;
    	return;
    }

    for(int i = 0; i < sz(point); i++){
    	Point a = point[i], b = point[(i+1)%sz(point)];
		double rise = a.y - b.y, run = a.x - b.x, det = b.y * run - b.x * rise;
    	double A = rise / det, B = -(run / det);
    	double perpendicular_distance = 1.0 / sqrt(A * A + B * B);
    	double theta = acos(perpendicular_distance / r);
    	double area = (theta * r * r - perpendicular_distance * r * sin(theta));
    	ans = max(ans , area);
    }
    cout << ans << endl;
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