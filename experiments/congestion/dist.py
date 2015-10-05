from numpy import array,histogram,median
from scipy.stats import linregress
from scipy.stats import norm

def fit_piecewise_linear_dist(values):
    hist,bins=histogram(values,100)    
    bin_centers=[(bins[i+1]+bins[i])/2. for i in range(len(bins)-1)]
    median_=median(values)
    for i in range(len(bin_centers)):
        if bin_centers[i] > median_:
            median_bin=i
            break
    le_median_out=array(hist[:median_bin])
    le_median_in=array(bin_centers[:median_bin])
    gt_median_out=array(hist[median_bin:])
    gt_median_in=array(bin_centers[median_bin:])
    le_params=linregress(le_median_in,le_median_out)
    gt_params=linregress(gt_median_in,gt_median_out)

    return le_params[:2],gt_params[:2]

samp = norm.rvs(loc=0,scale=1,size=1500) 

print fit_piecewise_linear_dist(samp)
